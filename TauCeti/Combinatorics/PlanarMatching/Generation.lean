/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Monoidal
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity
import all TauCeti.Combinatorics.PlanarMatching.Tensor

/-!
# Generation of Temperley–Lieb diagrams

An arc joining consecutive boundary points can be removed and reinserted as an elementary
cap, cup or identity strand, depending on its position relative to the two boundaries.
`TauCeti.TLDiagCat.hom_induction` uses this reduction to show that cups, caps and identities
generate all morphisms under composition and juxtaposition. On the empty boundary the only data
are the stored circles, each of which is a cup followed by a cap.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

namespace TauCeti

namespace PlanarMatching

private theorem paired_insFn_contract {k c : ℕ} (x : PlanarMatching (k + 2))
    (hc : c + 1 < k + 2) (h : pv x c = c + 1) :
    insFn c 2 (pv (x.contract ⟨c, by omega⟩)) (pv (nested 1)) = pv x := by
  have hr := pv_pv x (by omega : c < k + 2)
  rw [h] at hr
  funext q
  rcases exists_eq_ins_or_add c 2 q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · have hs : skipN c u = ins c 2 u := rfl
    have hn₁ : ins c 2 u ≠ c := by simp only [ins]; split_ifs <;> omega
    have hn₂ : ins c 2 u ≠ c + 1 := by simp only [ins]; split_ifs <;> omega
    have hp₁ : pv x (ins c 2 u) ≠ c := fun e => by
      have := congrArg (pv x) e
      rw [pv_pv_eq, h] at this
      exact hn₂ this
    have hp₂ : pv x (ins c 2 u) ≠ c + 1 := fun e => by
      have := congrArg (pv x) e
      rw [pv_pv_eq, hr] at this
      exact hn₁ this
    rw [insFn_ins, pv_contract_eq, contractFn_apply, hs, rejoin_of_ne _ hp₁ hp₂]
    generalize he : pv x (ins c 2 u) = w at hp₁ hp₂ ⊢
    simp only [unskipN, ins]
    split_ifs <;> omega
  · rw [insFn_add _ _ hv, pv_nested 1 hv]
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    · simpa using h.symm
    · simpa using hr.symm

/-- Inserting a single arc into a matching obtained by deleting that same arc recovers the
original matching. The arc joins the points numbered `a` and `a + 1`. -/
theorem insertBlock_contract_eq_of_partner {a b : ℕ} (x : PlanarMatching (a + 2 + b))
    (h : (x.val.val ⟨a, by omega⟩ : ℕ) = a + 1) :
    ((cast (k' := a + b + 2) (by omega) x).contract ⟨a, by omega⟩).insertBlock (nested 1) = x := by
  apply eq_of_pv_eq
  rw [pv_insertBlock]
  have hp : pv x a = a + 1 := by rwa [pv_of_lt _ (by omega : a < a + 2 + b)]
  exact (paired_insFn_contract (cast (k' := a + b + 2) (by omega) x) (c := a) (by omega)
    ((congrFun (pv_cast_eq _ x) a).trans hp)).trans (pv_cast_eq _ x)

private theorem insFn_end_eq_appendFn {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l) :
    insFn k l (pv x) (pv y) = appendFn k l (pv x) (pv y) := by
  funext q
  by_cases hq : q < k
  · rw [appendFn_of_lt _ _ hq, insFn, ite_eq_left hq, ins_of_lt (pv_lt x hq)]
  · by_cases h : q < k + l
    · rw [appendFn_of_le_of_lt _ _ (by omega) h, insFn, ite_eq_right hq, ite_eq_left h]
    · rw [appendFn_of_le _ _ (by omega), insFn, ite_eq_right hq, ite_eq_right h,
        pv_of_le x (by omega), ins_of_le (by omega)]
      omega

private theorem insFn_zero_eq_appendFn {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l) :
    insFn 0 k (pv y) (pv x) = appendFn k l (pv x) (pv y) := by
  funext q
  by_cases hq : q < k
  · simp [insFn, hq, appendFn_of_lt _ _ hq]
  · rw [insFn, ite_eq_right (Nat.not_lt_zero _), zero_add, ite_eq_right hq,
      ins_of_le (Nat.zero_le _)]
    by_cases h : q < k + l
    · rw [appendFn_of_le_of_lt _ _ (by omega) h, Nat.add_comm]
    · rw [appendFn_of_le _ _ (by omega), pv_of_le y (by omega)]
      omega

private theorem pv_append_insert_left {a b k l : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (z : PlanarMatching k) :
    pv ((x.insertBlock y).append z) =
      insFn a l (pv (x.append z)) (pv y) := by
  rw [pv_append_eq, ← insFn_zero_eq_appendFn, pv_insertBlock, pv_append_eq,
    ← insFn_zero_eq_appendFn, Nat.add_right_comm a l b,
    ← insFn_insFn_assoc (n := 0) (n' := a) _ _ y (by omega), zero_add]

private theorem pv_append_insert_right {a b k l : ℕ} (x : PlanarMatching k)
    (y : PlanarMatching (a + b)) (z : PlanarMatching l) :
    pv (x.append (y.insertBlock z)) = insFn (k + a) l (pv (x.append y)) (pv z) := by
  rw [pv_append_eq, ← insFn_end_eq_appendFn, pv_insertBlock, pv_append_eq,
    ← insFn_end_eq_appendFn, Nat.add_right_comm a l b,
    ← insFn_insFn_assoc (n' := a) _ _ z (by omega)]

end PlanarMatching

namespace TLDiagram

open PlanarMatching

/-- A cap with `a` straight strands to its left and `b` to its right. -/
def capAt (a b : ℕ) : TLDiagram (a + 2 + b) (a + b) :=
  ((id a).tensor cap).tensor (id b)

/-- A cup with `a` straight strands to its left and `b` to its right. -/
def cupAt (a b : ℕ) : TLDiagram (a + b) (a + 2 + b) :=
  ((id a).tensor cup).tensor (id b)

/-- The tensor expression for a cap at a specified position. -/
theorem capAt_def (a b : ℕ) : capAt a b = ((id a).tensor cap).tensor (id b) := (rfl)

/-- The tensor expression for a cup at a specified position. -/
theorem cupAt_def (a b : ℕ) : cupAt a b = ((id a).tensor cup).tensor (id b) := (rfl)

private theorem cap_matching : cap.matching = nested 1 := by
  apply PlanarMatching.ext
  simp only [cap_matching_val, nested_val]
  decide

private theorem cup_matching : cup.matching = nested 1 := by
  apply PlanarMatching.ext
  simp only [cup_matching_val, nested_val]
  decide

/-- The cap is inserted in the bottom boundary of the identity diagram. -/
@[simp]
theorem matching_capAt (a b : ℕ) :
    (capAt a b).matching = PlanarMatching.cast (by omega)
      ((PlanarMatching.cast (by omega : (a + b) + (a + b) = a + (b + (a + b)))
        (nested (a + b))).insertBlock (nested 1)) := by
  apply eq_of_pv_eq
  rw [capAt, pv_matching_tensor, pv_matching_tensor, pv_cast_eq, pv_insertBlock, pv_cast_eq,
    ← matching_id (a + b), ← id_tensor_id a b, pv_matching_tensor, cap_matching,
    insFn_insFn_eq, insFn_insFn_assoc (n' := 2) _ _ (id b).matching le_rfl,
    insFn_end_eq_appendFn]

/-- The cup is inserted in the top boundary of the identity diagram. -/
@[simp]
theorem matching_cupAt (a b : ℕ) :
    (cupAt a b).matching = PlanarMatching.cast (by omega)
      ((PlanarMatching.cast (by omega : (a + b) + (a + b) = (a + b + b) + a)
        (nested (a + b))).insertBlock (nested 1)) := by
  apply eq_of_pv_eq
  rw [cupAt, pv_matching_tensor, pv_matching_tensor, pv_cast_eq, pv_insertBlock, pv_cast_eq,
    ← matching_id (a + b), ← id_tensor_id a b, pv_matching_tensor, cup_matching,
    Nat.add_zero, insFn_insFn_eq, Nat.add_assoc a b b,
    insFn_insFn_assoc (n' := b + b) _ _ (nested 1) le_rfl, insFn_end_eq_appendFn]

/-- An elementary cap stores no closed circles. -/
@[simp]
theorem circles_capAt (a b : ℕ) : (capAt a b).circles = 0 := by simp [capAt_def]

/-- An elementary cup stores no closed circles. -/
@[simp]
theorem circles_cupAt (a b : ℕ) : (cupAt a b).circles = 0 := by simp [cupAt_def]

/-- Precomposing with a cap inserts one bottom arc and closes no circles. -/
theorem capAt_comp {a b p : ℕ} (f : TLDiagram (a + b) p) :
    (capAt a b).comp f = ⟨PlanarMatching.cast (by omega)
      ((PlanarMatching.cast (by omega : a + b + p = a + (b + p)) f.matching).insertBlock
        (nested 1)), f.circles⟩ := by
  have h := glueFn_insFn_of_le (c := a) (t := a + b) (by omega) (nested 1) (a + b) _
    ((id (a + b)).matching.append f.matching) (by omega)
  have ha : pv ((capAt a b).matching.append f.matching) =
      insFn a 2 (pv ((id (a + b)).matching.append f.matching)) (pv (nested 1)) := by
    rw [matching_capAt, pv_append_eq, pv_cast_eq]
    rw [show a + 2 + b + (a + b) = a + 2 + (b + (a + b)) by omega, ← pv_append_eq,
      pv_append_insert_left, pv_append_eq, pv_cast_eq, matching_id, pv_append_eq]
    congr 2; omega
  have hm : glueFn (a + b) (a + b) (pv ((id (a + b)).matching.append f.matching)) =
      pv f.matching := by rw [← pv_glueMiddle, matching_id, glueMiddle_nested_append]
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, ha, pv_cast_eq, pv_insertBlock, pv_cast_eq,
      Nat.add_right_comm a 2 b, h.1, hm]
  · have hz := h.2
    rw [← glueMiddleCircles_eq, matching_id, glueMiddleCircles_nested_append,
      ← Nat.add_right_comm a 2 b] at hz
    simp only [circles_comp, circles_capAt, zero_add, glueMiddleCircles_eq, ha, matching_id, hz,
      add_zero]

/-- Postcomposing with a cup inserts one top arc and closes no circles. -/
theorem comp_cupAt {n a b : ℕ} (f : TLDiagram n (a + b)) :
    f.comp (cupAt a b) = ⟨PlanarMatching.cast (by omega)
      ((PlanarMatching.cast (by omega : n + (a + b) = (n + b) + a)
        f.matching).insertBlock (nested 1)), f.circles⟩ := by
  have h := glueFn_insFn_of_lt (c := n) (t := n + b) (by omega) (l := 2)
    (pv (nested 1)) (a + b) _ (f.matching.append (id (a + b)).matching) (by omega)
  have ha : pv (f.matching.append (cupAt a b).matching) =
      insFn (n + b + 2 * (a + b)) 2
        (pv (f.matching.append (id (a + b)).matching)) (pv (nested 1)) := by
    rw [matching_cupAt, pv_append_eq, pv_cast_eq]
    rw [show a + b + (a + 2 + b) = (a + b + b) + 2 + a by omega, ← pv_append_eq,
      pv_append_insert_right, pv_append_eq, pv_cast_eq, matching_id, pv_append_eq]
    congr 1
    · omega
    · congr 1; omega
  have hm : glueFn n (a + b) (pv (f.matching.append (id (a + b)).matching)) =
      pv f.matching := by rw [← pv_glueMiddle, matching_id, glueMiddle_append_nested]
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, ha, h.1, hm, pv_cast_eq, pv_insertBlock, pv_cast_eq]
  · rw [circles_comp, circles_cupAt, add_zero, glueMiddleCircles_eq, ha,
      h.2, ← glueMiddleCircles_eq, matching_id, glueMiddleCircles_append_nested, add_zero]

private theorem exists_contracted_matching {k j c : ℕ} (x : PlanarMatching j)
    (hk : j = k + 2) (h : pv x c = c + 1) :
    ∃ y : PlanarMatching k, insFn c 2 (pv y) (pv (nested 1)) = pv x := by
  have hc : c < j := by
    by_contra! hc
    rw [pv_of_le x hc] at h
    omega
  have hpartner := pv_lt x hc
  rw [h] at hpartner
  subst j
  exact ⟨_, paired_insFn_contract x hpartner h⟩

private theorem exists_capAt_comp {a b m : ℕ} (f : TLDiagram (a + 2 + b) m)
    (h : pv f.matching a = a + 1) : ∃ g : TLDiagram (a + b) m, (capAt a b).comp g = f := by
  obtain ⟨y, hy⟩ := exists_contracted_matching (k := a + b + m) f.matching
    (by omega) h
  refine ⟨⟨y, f.circles⟩, ?_⟩
  rw [capAt_comp]
  ext : 1
  · apply eq_of_pv_eq
    rw [pv_cast_eq, pv_insertBlock, pv_cast_eq]
    exact hy
  · rfl

private theorem exists_comp_cupAt {n a b : ℕ} (f : TLDiagram n (a + 2 + b))
    (h : pv f.matching (n + b) = n + b + 1) :
    ∃ g : TLDiagram n (a + b), g.comp (cupAt a b) = f := by
  obtain ⟨y, hy⟩ := exists_contracted_matching (k := n + (a + b)) f.matching
    (by omega) h
  refine ⟨⟨y, f.circles⟩, ?_⟩
  rw [comp_cupAt]
  ext : 1
  · apply eq_of_pv_eq
    rw [pv_cast_eq, pv_insertBlock, pv_cast_eq]
    exact hy
  · rfl

private theorem exists_tensor_id_one {n m : ℕ} (f : TLDiagram (n + 1) (m + 1))
    (h : pv f.matching n = n + 1) : ∃ g : TLDiagram n m, g.tensor (id 1) = f := by
  obtain ⟨y, hy⟩ := exists_contracted_matching (k := n + m) f.matching
    (by omega) h
  refine ⟨⟨y, f.circles⟩, ?_⟩
  ext : 1
  · exact eq_of_pv_eq (by rw [pv_matching_tensor, matching_id]; exact hy)
  · simp

end TLDiagram

namespace TLDiagCat

open CategoryTheory MonoidalCategory
open PlanarMatching (pv pv_coe)

private theorem hom_induction_zero {motive : (of 0 ⟶ of 0) → Prop}
    (hId : motive (𝟙 (of 0))) (hCircle : motive circle)
    (hComp : ∀ {f g}, motive f → motive g → motive (f ≫ g)) (f : of 0 ⟶ of 0) : motive f := by
  have hp (k : ℕ) : motive ((End.of circle ^ k).asHom) := by
    induction k with
    | zero => simpa only [pow_zero, End.one_asHom] using hId
    | succ k ih => simpa only [pow_succ, End.mul_asHom] using hComp hCircle ih
  have he : f = (End.of circle ^ f.diagram.circles).asHom :=
    congrArg End.asHom (end_zero_eq_circle_pow (End.of f))
  exact he ▸ hp f.diagram.circles

private theorem mk_capAt (a b : ℕ) :
    (Hom.mk (TLDiagram.capAt a b) : of (a + 2 + b) ⟶ of (a + b)) =
      (𝟙 (of a) ⊗ₘ cap) ⊗ₘ 𝟙 (of b) := by
  apply hom_ext
  simp only [diagram_tensorHom, diagram_id, diagram_cap, TLDiagram.capAt_def]

private theorem mk_cupAt (a b : ℕ) :
    (Hom.mk (TLDiagram.cupAt a b) : of (a + b) ⟶ of (a + 2 + b)) =
      (𝟙 (of a) ⊗ₘ cup) ⊗ₘ 𝟙 (of b) := by
  apply hom_ext
  simp only [diagram_tensorHom, diagram_id, diagram_cup, TLDiagram.cupAt_def]

private theorem motive_id_of {motive : ∀ {X Y : TLDiagCat}, (X ⟶ Y) → Prop}
    (id_zero : motive (𝟙 (of 0))) (id_one : motive (𝟙 (of 1)))
    (tensor : ∀ {X Y X' Y'} {f : X ⟶ Y} {g : X' ⟶ Y'},
      motive f → motive g → motive (f ⊗ₘ g)) (n : ℕ) : motive (𝟙 (of n)) := by
  induction n with
  | zero => exact id_zero
  | succ n ih =>
    have he : of n ⊗ of 1 = of (n + 1) := TLDiagCat.ext (tensorObj_as (of n) (of 1))
    rw [← he]
    simpa only [id_tensorHom_id] using tensor ih id_one

/-- Every Temperley–Lieb morphism is generated by the cup, the cap, the empty diagram and the
straight strand under composition and tensor product. In particular, the same generators suffice
even when a diagram stores closed circles: each circle is a cup followed by a cap. -/
@[elab_as_elim]
theorem hom_induction {motive : ∀ {X Y : TLDiagCat}, (X ⟶ Y) → Prop}
    (id_zero : motive (𝟙 (of 0))) (id_one : motive (𝟙 (of 1)))
    (cup : motive TLDiagCat.cup) (cap : motive TLDiagCat.cap)
    (comp : ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z}, motive f → motive g → motive (f ≫ g))
    (tensor : ∀ {X Y X' Y'} {f : X ⟶ Y} {g : X' ⟶ Y'},
      motive f → motive g → motive (f ⊗ₘ g))
    {X Y : TLDiagCat} (f : X ⟶ Y) : motive f := by
  obtain ⟨n⟩ := X
  obtain ⟨m⟩ := Y
  suffices h : ∀ n m (D : TLDiagram n m), motive (Hom.mk D : of n ⟶ of m) by
    rw [← Hom.mk_diagram f]
    exact h n m f.diagram
  intro n m D
  induction hk : n + m using Nat.strong_induction_on generalizing n m with
  | ind k ih =>
    by_cases hzero : k = 0
    · obtain rfl : n = 0 := by omega
      obtain rfl : m = 0 := by omega
      apply hom_induction_zero id_zero _ comp
      rw [← cup_comp_cap]
      exact comp cup cap
    obtain ⟨a, ha⟩ := D.matching.exists_val_apply_eq_val_add_one (by omega)
    have hp : pv D.matching (a : ℕ) = (a : ℕ) + 1 := (pv_coe _ a).trans ha
    have ha' := a.isLt
    generalize hac : (a : ℕ) = c at hp ha'
    clear ha hac a
    -- The adjacent pair lies on the bottom, on the top, or across the right-hand corner.
    by_cases hb : c + 1 < n
    · obtain ⟨b, rfl⟩ : ∃ b, n = c + 2 + b := ⟨n - (c + 2), by omega⟩
      obtain ⟨g, rfl⟩ := TLDiagram.exists_capAt_comp D hp
      exact comp (f := Hom.mk (TLDiagram.capAt c b))
        (by
          rw [mk_capAt]
          exact tensor (tensor (motive_id_of id_zero id_one tensor _) cap)
            (motive_id_of id_zero id_one tensor _))
        (ih _ (by omega) _ _ g rfl)
    by_cases ht : n ≤ c
    · obtain ⟨b, rfl⟩ : ∃ b, c = n + b := ⟨c - n, by omega⟩
      have hpartner : n + b + 1 < n + m := by
        rw [← hp]
        exact PlanarMatching.pv_lt D.matching ha'
      obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 + b := ⟨m - (b + 2), by omega⟩
      obtain ⟨g, rfl⟩ := TLDiagram.exists_comp_cupAt D hp
      exact comp (g := Hom.mk (TLDiagram.cupAt a b)) (ih _ (by omega) _ _ g rfl)
        (by
          rw [mk_cupAt]
          exact tensor (tensor (motive_id_of id_zero id_one tensor _) cup)
            (motive_id_of id_zero id_one tensor _))
    · have hn : n = c + 1 := by omega
      subst n
      have hm : m ≠ 0 := by
        intro h
        have := PlanarMatching.pv_lt D.matching ha'
        omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      obtain ⟨g, rfl⟩ := TLDiagram.exists_tensor_id_one D hp
      exact tensor (ih _ (by omega) _ _ g rfl) id_one

end TLDiagCat

end TauCeti
