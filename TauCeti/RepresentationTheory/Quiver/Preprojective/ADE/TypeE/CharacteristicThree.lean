/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.ZMod.Basic

/-!
# A degree-six cyclic class of the `E₆` preprojective algebra in characteristic three

Let `x` be the backtrack `3 → 1 → 3` and `y` the backtrack `3 → 2 → 3`.
The branch-node word `y²x`, represented by the latest-vertex-first list
`[3, 2, 3, 2, 3, 1, 3]`, survives modulo additive commutators in characteristic three.
A linear functional supported on ten necklaces of length six detects it.
The necklace weights annihilate the local preprojective relations and are invariant under
rotation, so the functional descends to the cyclic quotient. The obstruction transfers to the
preprojective algebra of every orientation of the Bourbaki-labelled `E₆` diagram.

The quotient-functional construction follows the kernel descent used for the `D₄` Frobenius
functional in `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.SelfInjective`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Theorem 1.1 and Proposition 3.2, https://arxiv.org/abs/2301.06757.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

local notation "G" => diagramGraph (CartanMatrix.E 6)

/-- Signed necklaces supporting the degree-six trace; a missing necklace has weight zero. -/
private def e6Necklaces : List (List (Fin 6) × ZMod 3) :=
  [([0, 2, 3, 1, 3, 2], -1), ([0, 2, 3, 4, 3, 2], 1),
   ([1, 3, 2, 3, 2, 3], 1), ([1, 3, 2, 3, 4, 3], -1),
   ([1, 3, 4, 3, 2, 3], -1), ([1, 3, 4, 3, 4, 3], 1),
   ([1, 3, 4, 5, 4, 3], -1), ([2, 3, 2, 3, 4, 3], -1),
   ([2, 3, 4, 3, 4, 3], -1), ([2, 3, 4, 5, 4, 3], 1)]

private def e6Weight (l : List (Fin 6)) : ZMod 3 :=
  (e6Necklaces.map fun t => if l.IsRotated t.1 then t.2 else 0).sum

private theorem e6Weight_rotated {l m : List (Fin 6)} (h : l.IsRotated m) :
    e6Weight l = e6Weight m := by
  unfold e6Weight
  congr 1
  apply List.map_congr_left
  intro t _
  have ht : l.IsRotated t.1 ↔ m.IsRotated t.1 :=
    ⟨fun ht => h.symm.trans ht, fun ht => h.trans ht⟩
  simp only [ht]

private theorem e6Weight_eq_zero_of_length {l : List (Fin 6)} (h : l.length ≠ 6) :
    e6Weight l = 0 := by
  have hall : ∀ t ∈ e6Necklaces, t.1.length = 6 := by simp [e6Necklaces]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  apply ite_eq_right
  intro hr
  exact h (hr.perm.length_eq.trans (hall t ht))

-- The finite verification is partitioned by the initial vertex to respect the default limits.
private theorem e6Weight_backtrack_0 (a b c : Fin 6)
    (ha : (G).Adj 0 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 0) :
    ∑ w : Fin 6, (if (G).Adj 0 w then e6Weight [0, w, 0, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack_1 (a b c : Fin 6)
    (ha : (G).Adj 1 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 1) :
    ∑ w : Fin 6, (if (G).Adj 1 w then e6Weight [1, w, 1, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack_2 (a b c : Fin 6)
    (ha : (G).Adj 2 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 2) :
    ∑ w : Fin 6, (if (G).Adj 2 w then e6Weight [2, w, 2, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack_3 (a b c : Fin 6)
    (ha : (G).Adj 3 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 3) :
    ∑ w : Fin 6, (if (G).Adj 3 w then e6Weight [3, w, 3, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack_4 (a b c : Fin 6)
    (ha : (G).Adj 4 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 4) :
    ∑ w : Fin 6, (if (G).Adj 4 w then e6Weight [4, w, 4, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack_5 (a b c : Fin 6)
    (ha : (G).Adj 5 a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c 5) :
    ∑ w : Fin 6, (if (G).Adj 5 w then e6Weight [5, w, 5, a, b, c] else 0) = 0 := by
  fin_cases a <;> norm_num [diagramGraph_E_adj, EAdj] at ha
  all_goals fin_cases b <;> norm_num [diagramGraph_E_adj, EAdj] at hb
  all_goals fin_cases c <;> norm_num [diagramGraph_E_adj, EAdj] at hc <;>
    norm_num [diagramGraph_E_adj, EAdj] at hd
  all_goals decide

private theorem e6Weight_backtrack (v a b c : Fin 6)
    (ha : (G).Adj v a) (hb : (G).Adj a b)
    (hc : (G).Adj b c) (hd : (G).Adj c v) :
    ∑ w : Fin 6, (if (G).Adj v w then e6Weight [v, w, v, a, b, c] else 0) = 0 := by
  fin_cases v
  · exact e6Weight_backtrack_0 a b c ha hb hc hd
  · exact e6Weight_backtrack_1 a b c ha hb hc hd
  · exact e6Weight_backtrack_2 a b c ha hb hc hd
  · exact e6Weight_backtrack_3 a b c ha hb hc hd
  · exact e6Weight_backtrack_4 a b c ha hb hc hd
  · exact e6Weight_backtrack_5 a b c ha hb hc hd

variable (k : Type*) [CommRing k] [CharP k 3]

local notation "Q" => DoubledQuiver G
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "π" => signlessPreprojectiveMk k Q

open Classical in
private noncomputable def e6TraceAux : pathAlgebra k Q →ₗ[k] k :=
  liftLinear k fun x => if x.1 = x.2.1 then
    ZMod.castHom (dvd_refl 3) k (e6Weight
      (x.2.2.vertices.dropLast.map (vertexEquiv G).symm)) else 0

open Classical in
private theorem e6TraceAux_ofPath (x : Quiver.TotalPath Q) :
    e6TraceAux k (ofPath x) = if x.1 = x.2.1 then
      ZMod.castHom (dvd_refl 3) k (e6Weight
        (x.2.2.vertices.dropLast.map (vertexEquiv G).symm)) else 0 := by
  rw [e6TraceAux, liftLinear_ofPath]

private theorem e6TraceAux_mul_ofPath (x y : Quiver.TotalPath Q) :
    e6TraceAux k (ofPath x * ofPath y) = e6TraceAux k (ofPath y * ofPath x) := by
  classical
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst d
    by_cases hbc : b = c
    · subst c
      simp only [ofPath_mul_ofPath_of_comp, e6TraceAux_ofPath, ite_true,
        Path.vertices_comp, List.dropLast_append_of_ne_nil q.vertices_ne_nil,
        List.dropLast_append_of_ne_nil p.vertices_ne_nil, List.map_append]
      exact congrArg (ZMod.castHom (dvd_refl 3) k)
        (e6Weight_rotated List.isRotated_append)
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hbc,
        e6TraceAux_ofPath, map_zero]
      simp only [Ne.symm hbc, ite_false]
  · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]
    by_cases hbc : b = c
    · subst c
      rw [ofPath_mul_ofPath_of_comp, e6TraceAux_ofPath]
      simp only [Ne.symm hda, ite_false]
    · rw [ofPath_mul_ofPath_of_not_composable hbc, map_zero]

private theorem e6TraceAux_mul_comm (x y : pathAlgebra k Q) :
    e6TraceAux k (x * y) = e6TraceAux k (y * x) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']
  | single p a =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [add_mul, mul_add, map_add, hy, hy']
    | single q b =>
      simp only [single_eq_smul_ofPath, smul_mul_assoc, mul_smul_comm, map_smul,
        e6TraceAux_mul_ofPath, smul_smul, mul_comm]

private theorem e6TraceAux_ofPath_eq_zero (x : Quiver.TotalPath Q)
    (hx : x.2.2.length ≠ 6) : e6TraceAux k (ofPath x) = 0 := by
  rw [e6TraceAux_ofPath]
  split_ifs
  · rw [e6Weight_eq_zero_of_length, map_zero]
    simpa only [List.length_map, List.length_dropLast, Path.vertices_length,
      Nat.add_sub_cancel] using hx
  · rfl

private theorem e6TraceAux_relator_mul_ofPath (v : Fin 6)
    [Fintype (Quiver.Star (vertex G v))]
    (x : Quiver.TotalPath Q) :
    e6TraceAux k (signlessPreprojectiveRelator k (vertex G v) * ofPath x) = 0 := by
  classical
  let := Fintype.ofFinite ((G).neighborSet v)
  rw [signlessPreprojectiveRelator_congr k _ _ (instFintypeStarVertex G v),
    signlessPreprojectiveRelator_vertex, Finset.sum_mul, map_sum]
  obtain ⟨a, b, p⟩ := x
  by_cases hb : b = vertex G v
  swap
  · exact Finset.sum_eq_zero fun w _ => by
      rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_not_composable hb, map_zero]
  subst b
  by_cases ha : a = vertex G v
  swap
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp, e6TraceAux_ofPath]
    simp only [ha, ite_false]
  subst a
  -- A supported product must be closed and have a context of length four.
  by_cases hp : p.length = 4
  swap
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp]
    apply e6TraceAux_ofPath_eq_zero
    simpa only [Path.length_comp, backtrackPath_eq_comp, arrowPath_eq_toPath,
      Path.length_toPath] using (by omega : p.length + (1 + 1) ≠ 6)
  -- Decompose the four edges and apply the finite necklace identity.
  obtain ⟨a, e, q, hq, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p hp
  obtain ⟨b, f, r, hr, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ q hq
  obtain ⟨c, g, s, hs, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ r hr
  obtain ⟨d, h, t, ht, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ s hs
  cases t with
  | cons t l => simp at ht
  | nil =>
    obtain ⟨a, rfl⟩ := exists_eq_vertex G a
    obtain ⟨b, rfl⟩ := exists_eq_vertex G b
    obtain ⟨c, rfl⟩ := exists_eq_vertex G c
    have he := (nonempty_hom_iff G).1 ⟨e⟩
    have hf := (nonempty_hom_iff G).1 ⟨f⟩
    have hg := (nonempty_hom_iff G).1 ⟨g⟩
    have hh := (nonempty_hom_iff G).1 ⟨h⟩
    simp only [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp, e6TraceAux_ofPath,
      ite_true, Path.vertices_comp, backtrackPath_eq_comp, arrowPath_eq_toPath,
      Path.vertices_toPath, Path.vertices_nil, List.dropLast_cons_cons,
      List.dropLast_singleton, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, vertexEquiv_symm_vertex]
    rw [← map_sum]
    have hrot (w : Fin 6) : e6Weight [v, a, b, c, v, w] =
        e6Weight [v, w, v, a, b, c] :=
      e6Weight_rotated (List.isRotated_append (l := [v, a, b, c]) (l' := [v, w]))
    simp_rw [hrot]
    have hsum : (∑ w : (G).neighborSet v, e6Weight [v, (w : Fin 6), v, a, b, c]) = 0 := by
      have hh := e6Weight_backtrack v a b c he hf hg hh
      rw [← Finset.sum_filter, Finset.sum_subtype _
        (p := (· ∈ (G).neighborSet v)) (fun w => by simp)] at hh
      exact hh
    rw [hsum, map_zero]

private theorem e6TraceAux_relator_mul (v : Fin 6)
    [Fintype (Quiver.Star (vertex G v))]
    (x : pathAlgebra k Q) :
    e6TraceAux k (signlessPreprojectiveRelator k (vertex G v) * x) = 0 := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | single p a =>
    rw [single_eq_smul_ofPath, mul_smul_comm, map_smul,
      e6TraceAux_relator_mul_ofPath, smul_zero]

variable (neighborFintype : ∀ v : Fin 6, Fintype ((G).neighborSet v))

private theorem e6TraceAux_eq_zero {x : pathAlgebra k Q}
    (hx : letI := neighborFintype; π x = 0) :
    e6TraceAux k x = 0 := by
  let := neighborFintype
  rw [signlessPreprojectiveMk_eq_zero_iff, signlessPreprojectiveIdeal_eq_span] at hx
  suffices h : ∀ a b, e6TraceAux k (a * x * b) = 0 by simpa using h 1 1
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := exists_eq_vertex G v
    intro a b
    rw [mul_assoc, e6TraceAux_mul_comm, mul_assoc, e6TraceAux_relator_mul]
  | zero => simp
  | add x y _ _ hx hy => intro a b; rw [mul_add, add_mul, map_add, hx, hy, add_zero]
  | neg x _ hx => intro a b; rw [mul_neg, neg_mul, map_neg, hx, neg_zero]
  | left_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx (a * c) b
  | right_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx a (c * b)

private noncomputable def e6Trace : letI := neighborFintype; Π →ₗ[k] k := by
  let := neighborFintype
  exact ((π).toLinearMap.liftOfSurjective (signlessPreprojectiveMk_surjective k Q))
    ⟨e6TraceAux k, fun _ hx => LinearMap.mem_ker.mpr
      (e6TraceAux_eq_zero k neighborFintype (LinearMap.mem_ker.mp hx))⟩

private theorem e6Trace_mk (x : pathAlgebra k Q) : letI := neighborFintype;
    e6Trace k neighborFintype (π x) = e6TraceAux k x := by
  let := neighborFintype
  exact LinearMap.equivOfSurjective_apply _ _

private theorem e6Trace_mul_comm (x y : letI := neighborFintype; Π) :
    let := neighborFintype;
    e6Trace k neighborFintype (x * y) = e6Trace k neighborFintype (y * x) := by
  let := neighborFintype
  obtain ⟨x, rfl⟩ := signlessPreprojectiveMk_surjective k Q x
  obtain ⟨y, rfl⟩ := signlessPreprojectiveMk_surjective k Q y
  rw [← map_mul, ← map_mul, e6Trace_mk, e6Trace_mk, e6TraceAux_mul_comm]

private theorem e6Trace_cyclicWord : letI := neighborFintype;
    e6Trace k neighborFintype (signlessWord k G [3, 2, 3, 2, 3, 1, 3]) = 1 := by
  let := neighborFintype
  obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k («G» := G) 3 [2, 3, 2, 3, 1, 3]
    (by decide)
  have ha : a = 3 := by
    have hh := p.vertices_head?
    rw [hv] at hh
    simpa using congrArg (Option.map (vertexEquiv G).symm) hh.symm
  subst a
  rw [← hp, e6Trace_mk, e6TraceAux_ofPath]
  simp only [ite_true, hv]
  have hw : e6Weight [3, 1, 3, 2, 3, 2] = 1 := by decide
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.dropLast_cons_cons,
    List.dropLast_singleton, vertexEquiv_symm_vertex, hw, map_one]

omit [CharP k 3] in
/-- The closed branch-node word `y²x` in type `E₆` is homogeneous of path degree six.
The explicit neighbourhood enumeration preserves the caller's quotient carrier. -/
theorem signlessWord_E6_cyclicWord_mem_grade_six : letI := neighborFintype;
    signlessWord k G [3, 2, 3, 2, 3, 1, 3] ∈ signlessPreprojectiveGrade k Q 6 := by
  let := neighborFintype
  obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k («G» := G) 3 [2, 3, 2, 3, 1, 3]
    (by decide)
  rw [← hp]
  apply signlessPreprojectiveMk_mem_grade
  apply ofPath_mem_grade_of_length
  have hh := congrArg List.length hv
  simp only [Path.vertices_length, List.length_map, List.length_reverse,
    List.length_cons, List.length_nil] at hh
  exact (by omega : p.length = 6)

/-- In characteristic three the degree-six branch-node word `y²x` is not a sum of
commutators. The neighbourhood enumeration is retained as data in the quotient carrier. -/
theorem signlessWord_E6_cyclicWord_not_mem_commutatorSubmodule :
    let := neighborFintype;
    signlessWord k G [3, 2, 3, 2, 3, 1, 3] ∉ commutatorSubmodule k Π := by
  let := neighborFintype
  let : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) (by decide : 3 ≠ 1)
  dsimp only
  intro hw
  have hker := (commutatorSubmodule_le_ker_iff (e6Trace k neighborFintype)).2
    (e6Trace_mul_comm k neighborFintype)
  have hz := LinearMap.mem_ker.mp (hker hw)
  rw [e6Trace_cyclicWord] at hz
  exact one_ne_zero hz

/-- The explicit degree-six closed walk gives a nonzero cyclic class in characteristic three. -/
theorem mkQ_signlessWord_E6_cyclicWord_ne_zero :
    let := neighborFintype;
    (commutatorSubmodule k Π).mkQ (signlessWord k G [3, 2, 3, 2, 3, 1, 3]) ≠ 0 := by
  let := neighborFintype
  dsimp only
  intro h
  exact signlessWord_E6_cyclicWord_not_mem_commutatorSubmodule k neighborFintype
    ((Submodule.Quotient.mk_eq_zero _).mp h)

private theorem exists_preprojective_E6_cyclicClass (o : Orientation G)
    [instV : Fintype (OrientedQuiver G o)]
    [instHom : ∀ i j : OrientedQuiver G o, Fintype (i ⟶ j)] :
    ∃ x : preprojectiveAlgebra k (OrientedQuiver G o),
      x ∈ preprojectiveGrade k (OrientedQuiver G o) 6 ∧
        x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have hv : instV = OrientedQuiver.instFintypeOfFinite G o := Subsingleton.elim _ _
  cases hv
  have hh : instHom = OrientedQuiver.instFintypeHom G o := Subsingleton.elim _ _
  cases hh
  let neighborFintype (v : Fin 6) := Fintype.ofFinite ((G).neighborSet v)
  let := neighborFintype
  let C := eColoring G diagramGraph_E_adj
  let e := C.signlessPreprojectiveAlgebraEquiv k o
  let w := signlessWord k G [3, 2, 3, 2, 3, 1, 3]
  refine ⟨e w, C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o
    (signlessWord_E6_cyclicWord_mem_grade_six k neighborFintype), ?_⟩
  intro hw
  have hh := map_mem_commutatorSubmodule e.symm hw
  rw [AlgEquiv.symm_apply_apply] at hh
  exact signlessWord_E6_cyclicWord_not_mem_commutatorSubmodule k neighborFintype hh

/-- Every orientation of `E₆` has a degree-six class outside the commutator submodule in
characteristic three, with the caller's vertex and arrow enumerations retained. -/
theorem exists_mem_preprojectiveGrade_E6_six_notMem_commutatorSubmodule
    (o : Orientation (diagramGraph DynkinType.E6.cartanMatrix))
    [instV : Fintype (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)]
    [instHom : ∀ i j : OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o,
      Fintype (i ⟶ j)] :
    ∃ x : preprojectiveAlgebra k (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o),
      x ∈ preprojectiveGrade k (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o) 6 ∧
        x ∉ commutatorSubmodule k
          (preprojectiveAlgebra k
            (OrientedQuiver (diagramGraph DynkinType.E6.cartanMatrix) o)) := by
  have key : ∀ C : Matrix (Fin 6) (Fin 6) ℤ, C = CartanMatrix.E 6 →
      ∀ (o : Orientation (diagramGraph C))
        [Fintype (OrientedQuiver (diagramGraph C) o)]
        [∀ i j : OrientedQuiver (diagramGraph C) o, Fintype (i ⟶ j)],
      ∃ x : preprojectiveAlgebra k (OrientedQuiver (diagramGraph C) o),
        x ∈ preprojectiveGrade k (OrientedQuiver (diagramGraph C) o) 6 ∧
          x ∉ commutatorSubmodule k
            (preprojectiveAlgebra k (OrientedQuiver (diagramGraph C) o)) := by
    rintro C rfl
    exact exists_preprojective_E6_cyclicClass k
  exact @key _ DynkinType.cartanMatrix_E6 o instV instHom

end TauCeti
