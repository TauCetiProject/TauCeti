/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm
import TauCeti.RepresentationTheory.Quiver.Representation.AsModule

/-!
# Independence of type-`A` preprojective valley words

The bounded valley words in each corner of the signless preprojective algebra of `Aₙ`
form a basis, whose cardinality gives the dimension of the corner. A rectangular representation
detects these words: starting at vertex `a`, descents increment the first coordinate and ascents
increment the second. The rectangle has
`a + 1` rows and `n - a` columns. A descent carries the sign `(-1)^r`, where `r` is the
column, so the two backtracks cancel, including in characteristic two.

These corner bases supply the coordinates needed for the Frobenius pairing and projective
socles of the type-`A` preprojective algebra. Multiplication uses later-factor-first order.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius
  property and projective modules.
* The valley words and their spanning theorem are those of
  `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver CategoryTheory

variable (k : Type*) [Field k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Q" => DoubledQuiver AG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "π" => signlessPreprojectiveMk k Q

private noncomputable local instance : DecidableEq Q := Classical.decEq _

private abbrev Grid (k : Type*) [Field k] := (ℕ × ℕ) →₀ k

private noncomputable def gridStep (a : Fin (DynkinType.A n).rank) (i j : ℕ) :
    Module.End k (Grid k) :=
  Finsupp.linearCombination k fun x : ℕ × ℕ =>
    if x.1 ≤ a.val ∧ x.2 < n - a.val ∧ i + x.1 = a.val + x.2 then
      if j = i + 1 ∧ x.2 + 1 < n - a.val then
        Finsupp.single (x.1, x.2 + 1) 1
      else if i = j + 1 ∧ x.1 < a.val then
        (-1 : k) ^ x.2 • Finsupp.single (x.1 + 1, x.2) 1
      else 0
    else 0

private theorem gridStep_single (a : Fin (DynkinType.A n).rank) (i j s r : ℕ) (c : k) :
    gridStep k a i j (Finsupp.single (s, r) c) =
      if s ≤ a.val ∧ r < n - a.val ∧ i + s = a.val + r then
        if j = i + 1 ∧ r + 1 < n - a.val then Finsupp.single (s, r + 1) c
        else if i = j + 1 ∧ s < a.val then
          Finsupp.single (s + 1, r) ((-1 : k) ^ r * c) else 0
      else 0 := by
  classical
  simp only [gridStep, Finsupp.linearCombination_single]
  split_ifs <;> simp [mul_comm c]

private theorem gridStep_backtrack (a : Fin (DynkinType.A n).rank) (i j s r : ℕ)
    (h : i + 1 = j ∨ j + 1 = i) :
    gridStep k a j i (gridStep k a i j (Finsupp.single (s, r) 1)) =
      if s < a.val ∧ r + 1 < n - a.val ∧ i + s = a.val + r then
        (if j = i + 1 then -((-1 : k) ^ r) else (-1 : k) ^ r) •
          Finsupp.single (s + 1, r + 1) 1
      else 0 := by
  classical
  rcases h with h | h
  · subst j
    simp only [gridStep_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    grind [gridStep_single, pow_succ]
  · subst i
    simp only [gridStep_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    grind [gridStep_single]

private noncomputable def gridRep (a : Fin (DynkinType.A n).rank) : QuiverRep k Q :=
  Paths.lift {
    obj := fun _ => ModuleCat.of k (Grid k)
    map := fun {i j} _ => ModuleCat.ofHom (gridStep k a
      ((vertexEquiv AG).symm i).val ((vertexEquiv AG).symm j).val) }

/-- `Paths.lift` assigns `ModuleCat.of k (Grid k)` to every vertex. Thus its underlying
`QuiverRep.vertexSpace` reduces to `Grid k`; this equivalence records that identification. -/
private noncomputable def gridVertexEquiv (a : Fin (DynkinType.A n).rank) (i : Q) :
    Grid k ≃ₗ[k] QuiverRep.vertexSpace k Q (gridRep k a) i :=
  LinearEquiv.refl k _

private theorem gridRep_map_arrow (a : Fin (DynkinType.A n).rank) {i j : Q}
    (f : i ⟶ j) :
    (gridRep k a).map f.toPath = ModuleCat.ofHom (gridStep k a
      ((vertexEquiv AG).symm i).val ((vertexEquiv AG).symm j).val) :=
  Paths.lift_toPath _ _

private theorem gridRep_arrow (a : Fin (DynkinType.A n).rank) {i j : Q} (f : i ⟶ j)
    (x : Grid k) :
    QuiverRep.mapₗ k Q (gridRep k a) f.toPath (gridVertexEquiv k a i x) =
      gridVertexEquiv k a j
        (gridStep k a ((vertexEquiv AG).symm i).val ((vertexEquiv AG).symm j).val x) := by
  rw [QuiverRep.mapₗ_apply, gridRep_map_arrow]
  -- `gridVertexEquiv` is the underlying identity of each constant `ModuleCat.of` object.
  rfl

private theorem gridRep_backtrack (a i : Fin (DynkinType.A n).rank) (s r : ℕ) :
    (∑ w : (AG).neighborSet i,
      QuiverRep.mapₗ k Q (gridRep k a)
        (backtrackPath AG (((AG).mem_neighborSet i w).1 w.2)))
          (gridVertexEquiv k a (vertex AG i) (Finsupp.single (s, r) 1)) = 0 := by
  classical
  simp only [LinearMap.sum_apply, backtrackPath_eq_comp,
    arrowPath_eq_toPath, QuiverRep.mapₗ_comp, LinearMap.comp_apply, gridRep_arrow,
    vertexEquiv_symm_vertex]
  rw [← map_sum (gridVertexEquiv k a (vertex AG i)), ← map_zero (gridVertexEquiv k a (vertex AG i))]
  apply (gridVertexEquiv k a (vertex AG i)).injective
  have hn := DynkinType.rank_A n
  have ha := a.isLt
  have hi := i.isLt
  have hadj (j : (AG).neighborSet i) : i.val + 1 = j.val.val ∨ j.val.val + 1 = i.val :=
    (diagramGraph_A_adj n i j.val).1 (((AG).mem_neighborSet i j).1 j.property)
  simp_rw [gridStep_backtrack k a _ _ s r (hadj _)]
  by_cases h : s < a.val ∧ r + 1 < n - a.val ∧ i.val + s = a.val + r
  · have hi : 0 < i.val ∧ i.val + 1 < (DynkinType.A n).rank := by omega
    let lo : (AG).neighborSet i := ⟨⟨i.val - 1, by omega⟩, by
      apply (SimpleGraph.mem_neighborSet _ _ _).2
      apply (diagramGraph_A_adj n _ _).2
      right; dsimp; omega⟩
    let up : (AG).neighborSet i := ⟨⟨i.val + 1, hi.2⟩, by
      apply (SimpleGraph.mem_neighborSet _ _ _).2
      apply (diagramGraph_A_adj n _ _).2
      left; rfl⟩
    have hcases (j : (AG).neighborSet i) : j = lo ∨ j = up := by
      rcases hadj j with hj | hj
      · right; apply Subtype.ext; apply Fin.ext; exact hj.symm
      · left; apply Subtype.ext; apply Fin.ext; dsimp [lo]; omega
    have hne : lo ≠ up := by
      intro he; have := congrArg (fun x : (AG).neighborSet i => x.val.val) he
      dsimp [lo, up] at this; omega
    rw [Finset.sum_eq_add_of_mem lo up (Finset.mem_univ lo) (Finset.mem_univ up) hne
      (fun j _ hj => (hcases j).elim (fun he => (hj.1 he).elim) (fun he => (hj.2 he).elim))]
    simp [h, lo, up, show ¬i.val - 1 = i.val + 1 by omega]
  · simp [h]

private theorem gridRep_relator (a : Fin (DynkinType.A n).rank) (v : Q) :
    QuiverRep.toEnd k Q (gridRep k a) (signlessPreprojectiveRelator k v) = 0 := by
  classical
  obtain ⟨i, rfl⟩ := exists_eq_vertex AG v
  rw [signlessPreprojectiveRelator_congr k (vertex AG i) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum]
  simp only [backtrackElem_eq_ofPath, QuiverRep.toEnd_ofPath]
  have hzero : (∑ w : (AG).neighborSet i,
      QuiverRep.mapₗ k Q (gridRep k a)
        (backtrackPath AG (((AG).mem_neighborSet i w).1 w.2))) = 0 := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (gridVertexEquiv k a (vertex AG i)).surjective z
    induction x using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | single x c =>
      obtain ⟨s, r⟩ := x
      rw [← Finsupp.smul_single_one (s, r) c]
      simp only [map_smul, gridRep_backtrack, smul_zero, LinearMap.zero_apply]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sum_apply, QuiverRep.pathEnd_apply]
  rw [← map_sum (DirectSum.lof k Q (QuiverRep.vertexSpace k Q (gridRep k a))
    (vertex AG i))]
  have hz := LinearMap.congr_fun hzero
    (DirectSum.component k Q (QuiverRep.vertexSpace k Q (gridRep k a)) (vertex AG i) z)
  simpa only [LinearMap.sum_apply, LinearMap.zero_apply, map_zero] using
    congrArg (DirectSum.lof k Q (QuiverRep.vertexSpace k Q (gridRep k a)) (vertex AG i)) hz

private noncomputable def gridAction (a : Fin (DynkinType.A n).rank) :=
  signlessPreprojectiveLift (QuiverRep.toEnd k Q (gridRep k a)) (gridRep_relator k a)

private noncomputable def gridVector (a i : Fin (DynkinType.A n).rank) (s r : ℕ) :=
  DirectSum.lof k Q (QuiverRep.vertexSpace k Q (gridRep k a)) (vertex AG i)
    (gridVertexEquiv k a (vertex AG i) (Finsupp.single (s, r) 1))

private theorem gridAction_vertex (a i : Fin (DynkinType.A n).rank) (s r : ℕ) :
    gridAction k a (π (vertexIdempotent k (vertex AG i))) (gridVector k a i s r) =
      gridVector k a i s r := by
  rw [gridAction, signlessPreprojectiveLift_signlessPreprojectiveMk,
    QuiverRep.toEnd_vertexIdempotent, QuiverRep.pathEnd_apply, QuiverRep.mapₗ_nil]
  simp only [gridVector, DirectSum.component.lof_self, LinearMap.id_apply]

private theorem gridAction_arrow (a i j : Fin (DynkinType.A n).rank) (s r : ℕ)
    (h : (AG).Adj i j) :
    gridAction k a (signlessArrow k AG i j) (gridVector k a i s r) =
      DirectSum.lof k Q (QuiverRep.vertexSpace k Q (gridRep k a)) (vertex AG j)
        (gridVertexEquiv k a (vertex AG j)
          (gridStep k a i j (Finsupp.single (s, r) 1))) := by
  rw [signlessArrow_of_adj k h, gridAction,
    signlessPreprojectiveLift_signlessPreprojectiveMk, ofArrow_eq_ofPath,
    QuiverRep.toEnd_ofPath, QuiverRep.pathEnd_apply]
  simp only [gridVector, DirectSum.component.lof_self, gridRep_arrow,
    vertexEquiv_symm_vertex]

private theorem gridAction_descent (a : Fin (DynkinType.A n).rank) (m s : ℕ)
    (hs : m + s = a.val) (hm : m < (DynkinType.A n).rank) :
    gridAction k a (ladderValley (fun w => signlessArrow k AG w (w + 1))
      (fun w => signlessArrow k AG (w + 1) w) m s 0) (gridVector k a a 0 0) =
        gridVector k a ⟨m, hm⟩ s 0 := by
  induction s generalizing m with
  | zero =>
    have heq : (⟨m, hm⟩ : Fin (DynkinType.A n).rank) = a := Fin.ext (by omega)
    simp only [ladderValley_zero_zero, map_one, Module.End.one_apply, heq]
  | succ s ih =>
    have hm' : m + 1 < (DynkinType.A n).rank := by omega
    rw [← d_mul_ladderValley_succ_zero, map_mul, Module.End.mul_apply,
      ih (m + 1) (by omega) hm']
    have harr := gridAction_arrow k a ⟨m + 1, hm'⟩ ⟨m, hm⟩ s 0
      ((diagramGraph_A_adj n _ _).2 (.inr rfl))
    have ha : a.val < n := by simpa only [DynkinType.rank_A] using a.isLt
    have ha0 : 0 < n - a.val := by omega
    have hs' : s < a.val := by omega
    have hs'' : s ≤ a.val := by omega
    simpa only [gridStep_single, hs'', hs', ha0,
      Nat.add_zero, hs, show m + 1 + s = a.val by omega, and_self,
      ite_true, show ¬ m = m + 1 + 1 by omega, false_and, ite_false,
      pow_zero, mul_one, gridVector] using harr

private theorem gridAction_valley (a : Fin (DynkinType.A n).rank) (m s r : ℕ)
    (hs : m + s = a.val) (hr : r < n - a.val)
    (hmr : m + r < (DynkinType.A n).rank) :
    gridAction k a (ladderValley (fun w => signlessArrow k AG w (w + 1))
      (fun w => signlessArrow k AG (w + 1) w) m s r) (gridVector k a a 0 0) =
        gridVector k a ⟨m + r, hmr⟩ s r := by
  induction r with
  | zero => simpa only [Nat.add_zero] using gridAction_descent k a m s hs hmr
  | succ r ih =>
    have hmr' : m + r < (DynkinType.A n).rank := by omega
    rw [← u_mul_ladderValley, map_mul, Module.End.mul_apply,
      ih (by omega) hmr']
    have harr := gridAction_arrow k a ⟨m + r, hmr'⟩ ⟨m + (r + 1), hmr⟩ s r
      ((diagramGraph_A_adj n _ _).2 (.inl (by dsimp; omega)))
    have hs' : s ≤ a.val := by omega
    have hi : m + r + s = a.val + r := by omega
    have hr' : r < n - a.val := by omega
    simpa only [gridStep_single, hs', hr', hi,
      show m + (r + 1) = m + r + 1 by omega, hr,
      and_self, ite_true, gridVector] using harr

private theorem gridAction_bounded_valley (a b : Fin (DynkinType.A n).rank) (m : ℕ)
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    gridAction k a (signlessPreprojectiveAValley k a b m) (gridVector k a a 0 0) =
      gridVector k a b (a.val - m) (b.val - m) := by
  have hn := DynkinType.rank_A n
  have ha := a.isLt
  have hb := b.isLt
  have hm' := Finset.mem_Icc.mp hm
  have hs : m + (a.val - m) = a.val := by omega
  have hr : b.val - m < n - a.val := by omega
  have hmr : m + (b.val - m) < (DynkinType.A n).rank := by omega
  have heq : (⟨m + (b.val - m), hmr⟩ : Fin (DynkinType.A n).rank) = b :=
    Fin.ext (by dsimp; omega)
  rw [signlessPreprojectiveAValley_def, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, gridAction_vertex, gridAction_valley k a m _ _ hs hr hmr, heq,
    gridAction_vertex]

private noncomputable def gridDetect (a b : Fin (DynkinType.A n).rank) : Π →ₗ[k] Grid k where
  toFun x := (gridVertexEquiv k a (vertex AG b)).symm
    (DirectSum.component k Q (QuiverRep.vertexSpace k Q (gridRep k a)) (vertex AG b)
      (gridAction k a x (gridVector k a a 0 0)))
  map_add' x y := by simp only [map_add, LinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem gridDetect_valley (a b : Fin (DynkinType.A n).rank) (m : ℕ)
    (hm : m ∈ Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) :
    gridDetect k a b (signlessPreprojectiveAValley k a b m) =
      Finsupp.single (a.val - m, b.val - m) 1 := by
  simp only [gridDetect, LinearMap.coe_mk, AddHom.coe_mk]
  rw [gridAction_bounded_valley k a b m hm]
  simp only [gridVector, DirectSum.component.lof_self, LinearEquiv.symm_apply_apply]

/-- The bounded valley classes in a type-`A` corner are linearly independent over every field.
Together with the corner spanning theorem, this gives the complete corner normal form. -/
theorem linearIndependent_signlessPreprojectiveAValley_Icc (a b : Fin (DynkinType.A n).rank) :
    LinearIndependent k (fun m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) =>
      signlessPreprojectiveAValley k a b m.val) := by
  apply LinearIndependent.of_comp (gridDetect k a b)
  have hinj : Function.Injective
      (fun m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) =>
        (a.val - m.val, b.val - m.val)) := by
    intro m l h
    have hm := Finset.mem_Icc.mp m.property
    have hl := Finset.mem_Icc.mp l.property
    have heq := congrArg Prod.fst h
    apply Subtype.ext
    dsimp only at heq
    omega
  simpa only [Function.comp_def, gridDetect_valley k a b _ (Subtype.property _)] using
    (Finsupp.linearIndependent_single_one (R := k) (ι := ℕ × ℕ)).comp _ hinj

/-- The basis of `e_b Π e_a` consisting of the valleys with
`a + b + 1 - n ≤ m ≤ min a b`. The lower bound uses natural-number subtraction. -/
noncomputable def signlessPreprojectiveACornerBasis (a b : Fin (DynkinType.A n).rank) :
    Module.Basis ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val)) k
      (cornerSubmodule k (π (vertexIdempotent k (vertex AG b)))
        (π (vertexIdempotent k (vertex AG a)))) :=
  (Module.Basis.span (linearIndependent_signlessPreprojectiveAValley_Icc k a b)).map
    (LinearEquiv.ofEq _ _ (by
      rw [cornerSubmodule_signlessPreprojective_A_eq_span_valley,
        Set.image_eq_range]
      rfl))

/-- The corner basis vector is the indicated bounded valley class. -/
@[simp]
theorem coe_signlessPreprojectiveACornerBasis_apply (a b : Fin (DynkinType.A n).rank)
    (m : ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))) :
    (signlessPreprojectiveACornerBasis k a b m : Π) =
      signlessPreprojectiveAValley k a b m := by
  rw [signlessPreprojectiveACornerBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- The dimension of the type-`A` corner is the number of its bounded valleys. -/
@[simp]
theorem finrank_cornerSubmodule_signlessPreprojective_A (a b : Fin (DynkinType.A n).rank) :
    Module.finrank k (cornerSubmodule k (π (vertexIdempotent k (vertex AG b)))
      (π (vertexIdempotent k (vertex AG a)))) =
        min a.val b.val + 1 - (a.val + b.val + 1 - n) := by
  rw [Module.finrank_eq_nat_card_basis (signlessPreprojectiveACornerBasis k a b),
    Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_Icc]

end TauCeti
