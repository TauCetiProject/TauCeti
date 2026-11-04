/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Necklace

/-!
# A degree-ten cyclic class of the `E₈` preprojective algebra in characteristic five

In the Bourbaki labelling of `E₈` (`TauCeti.zigzagE8Graph`), the node `3` is the branch node;
write `y` for the backtrack `3 → 2 → 3` into the arm `2, 0` and `z` for the backtrack
`3 → 4 → 3` into the long arm `4, 5, 6, 7`. The closed walk `y z⁴`, listed latest vertex first
as `[3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3]`, has path degree ten. In characteristic five it is not a
sum of commutators in the signless preprojective algebra `Π⁺(E₈)`, so its class in the cyclic
quotient `Π⁺(E₈) / [Π⁺(E₈), Π⁺(E₈)]` is nonzero. Through the bipartite sign rescaling the same
holds in the additive preprojective algebra of every orientation of `E₈`.

Five is the bad characteristic special to `E₈`: by
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.CyclicQuotient`, the cyclic quotient
of `Π⁺(E₈)` is concentrated in degree zero as soon as `2`, `3` and `5` are units, and this
file shows that the hypothesis on `5` cannot be dropped. Characteristic two is treated in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.BadCharacteristic`. In Liu and
Wang's comparison, the degree-ten piece of the cyclic quotient is the Hochschild cohomology
`HH^{2,8}` of the two-dimensional Ginzburg algebra, the space controlling the corresponding
`A∞` deformations of the zigzag algebra of `E₈`. No Hochschild comparison or nonformality
statement is proved here.

## The argument

Positive-degree elements of the finite-dimensional algebra `Π⁺(E₈)` are nilpotent, so traces
of matrix representations cannot detect them. Instead the class is detected by a necklace
functional, `TauCeti.signlessNecklaceFunctional`: a weight on the cyclic words of closed walks
of length ten which satisfies the signless necklace relations `∑_{w ∼ v} W (v w L) = 0` for every
closed walk `L` of length eight at every vertex `v`. Such weights are the linear functionals on
the degree-ten piece of the cyclic quotient. The weight used here was found by solving these
linear relations over `ZMod 5` by computer; it is supported on `84` necklaces and takes the value
one on the necklace of `y z⁴`. It is recorded below by integer representatives, indexed by a
numerical code of the necklace, and its relations, one for each closed walk of length eight, are
verified modulo five by a single kernel computation over an explicit enumeration of the walks.

## Main results

* `TauCeti.signlessWord_E8_cyclicWord_mem_grade_ten`: the closed walk `y z⁴` has path degree
  ten.
* `TauCeti.signlessWord_E8_cyclicWord_notMem_commutatorSubmodule` and
  `TauCeti.mkQ_signlessWord_E8_cyclicWord_ne_zero`: when `5 = 0`, it is not a sum of
  commutators in `Π⁺(E₈)`, and its class in the cyclic quotient is nonzero.
* `TauCeti.exists_mem_preprojectiveGrade_E8_ten_notMem_commutatorSubmodule`: when `5 = 0`,
  the preprojective algebra of every orientation of `E₈` has a degree-ten element which is not
  a sum of commutators.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, https://arxiv.org/abs/math/0609006, for the cyclic quotient of a Dynkin
  preprojective algebra in positive characteristic.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Theorem 1.1, for the bad characteristics of `E₈` and the
  role of the cyclic quotient in the deformation theory of zigzag algebras.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] eNeighborSetFintype

/-! ### Walks of the `E₈` graph -/

/-- The neighbours of each vertex of the Bourbaki-labelled `E₈` graph, in increasing order. -/
private def e8Neighbors (v : Fin 8) : List (Fin 8) :=
  ![[2], [3], [0, 3], [1, 2, 4], [3, 5], [4, 6], [5, 7], [6]] v

private theorem zigzagE8Graph_adj_iff_mem_e8Neighbors (v w : Fin 8) :
    zigzagE8Graph.Adj v w ↔ w ∈ e8Neighbors v := by
  rw [zigzagE8Graph_adj]
  revert v w
  decide

private theorem nodup_e8Neighbors (v : Fin 8) : (e8Neighbors v).Nodup := by
  revert v
  decide

/-- The walks with `n` steps from `v` in the `E₈` graph, each listed from `v`. These are plain
lists rather than the walks of `SimpleGraph.finsetWalkLength`, so that the kernel can evaluate
the check `e8ListWeight_relations` below without deduplicating finite sets of walks. -/
private def e8Walks : ℕ → Fin 8 → List (List (Fin 8))
  | 0, v => [[v]]
  | n + 1, v => (e8Neighbors v).flatMap fun w => (e8Walks n w).map (v :: ·)

/-- Every walk with `n` steps from `v` is enumerated by `e8Walks n v`. -/
private theorem mem_e8Walks (n : ℕ) (v : Fin 8) (l : List (Fin 8)) (hl : l.length = n + 1)
    (hv : l.head? = some v) (hc : l.IsChain zigzagE8Graph.Adj) : l ∈ e8Walks n v := by
  induction n generalizing v l with
  | zero =>
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    obtain rfl : a = v := by simpa using hv
    simp [e8Walks]
  | succ n ih =>
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    obtain rfl : a = v := by simpa using hv
    obtain ⟨b, l, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hl)
    obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
    rw [e8Walks, List.mem_flatMap]
    exact ⟨b, (zigzagE8Graph_adj_iff_mem_e8Neighbors a b).mp hab,
      List.mem_map_of_mem (ih b _ (by simpa using hl) rfl hc)⟩

/-! ### The necklace weight -/

/-- A numerical code of a list of vertices, read as the digits of a number in base eight. -/
private def e8Code (l : List (Fin 8)) : ℕ :=
  l.foldr (fun a c => a.val + 8 * c) 0

/-- The largest code of a rotation of a list of vertices; it depends only on the necklace. -/
private def e8Key (l : List (Fin 8)) : ℕ :=
  (l.cyclicPermutations.map e8Code).foldr max 0

/-- The integer representatives, in `[-2, 2]`, of the nonzero values modulo five of the
degree-ten necklace weight, indexed by the keys of their necklaces. -/
private def e8Table : List (ℕ × ℤ) :=
  [(442867865, -2), (443127449, 2), (590152907, 2), (590164691, -2), (590165195, -2),
   (590230227, 2), (591475411, 2), (592229395, 2), (592229579, -2), (592229587, -2),
   (592230603, 2), (592261843, -2), (592327379, 2), (592327699, -2), (592327883, 2),
   (592327891, 2), (596423699, -2), (596423883, 2), (596423891, 2), (596424907, -2),
   (596424915, -2), (596444363, -2), (596456147, -1), (596456651, 2), (596457675, -2),
   (596457683, 1), (596521683, 1), (596522003, 2), (596522187, 1), (596522195, -2),
   (596523211, -1), (596523219, 1), (744857756, 2), (744859228, -2), (744859292, -2),
   (744859420, -1), (744867420, 2), (744867484, 2), (744867612, 1), (745023068, 2),
   (745023260, -2), (745117340, 1), (745117468, -1), (745121372, -2), (745121564, 2),
   (745129564, 2), (745129628, -1), (745129756, -1), (745641628, -1), (745641756, 1),
   (745644188, -2), (745645660, -1), (745645724, 2), (745645852, -1), (745653852, 1),
   (745653916, -1), (745719388, -1), (745719452, 1), (749835932, 1), (749836060, -1),
   (749838492, 2), (749839964, 1), (749840028, -2), (749840156, 1), (749848156, -1),
   (749848220, 1), (749913692, 1), (749913756, -1), (898413797, -1), (898414821, 1),
   (898414949, -1), (898434277, -2), (898446053, -1), (898446565, 2), (898447589, -1),
   (898447717, 1), (898511589, 1), (898512101, -1), (899035877, -1), (899036389, 1),
   (903230181, 1), (903230693, -1), (1051825966, -1), (1051830062, 1)]

/-- The degree-ten necklace weight on lists of vertices: zero off length ten, and otherwise read
from `e8Table` by the key of the necklace. -/
private def e8ListWeight (l : List (Fin 8)) : ℤ :=
  if l.length = 10 then (e8Table.lookup (e8Key l)).getD 0 else 0

private theorem e8ListWeight_eq_of_isRotated {l m : List (Fin 8)} (h : l ~r m) :
    e8ListWeight l = e8ListWeight m := by
  have hkey : e8Key l = e8Key m := (h.cyclicPermutations.perm.map e8Code).foldr_eq 0
  simp only [e8ListWeight, hkey, h.perm.length_eq]

/-- The signless necklace relations of the weight, checked modulo five on every closed walk of
length eight. -/
private theorem e8ListWeight_relations : ((List.finRange 8).all fun v => (e8Walks 8 v).all fun l =>
    l.getLast? != some v ||
      ((e8Neighbors v).map fun w => e8ListWeight (v :: w :: l.dropLast)).sum % 5 == 0) =
      true := by
  decide +kernel

variable (k : Type*) [CommRing k]

/-- The degree-ten necklace weight of `E₈`, with values in `k`. -/
private def e8Weight : Cycle (Fin 8) → k :=
  Quotient.lift (fun l => (e8ListWeight l : k)) fun _ _ h =>
    congrArg _ (e8ListWeight_eq_of_isRotated h)

private theorem e8Weight_coe (l : List (Fin 8)) :
    e8Weight k (l : Cycle (Fin 8)) = e8ListWeight l :=
  rfl

/-- In characteristic five the degree-ten weight satisfies the signless necklace relations. -/
private theorem isSignlessNecklaceWeight_e8Weight (h5 : (5 : k) = 0) :
    IsSignlessNecklaceWeight zigzagE8Graph (e8Weight k) := by
  refine (isSignlessNecklaceWeight_iff _ _).mpr fun v L hL hv => ?_
  -- The sum over the neighbourhood is the sum over the explicit list of neighbours.
  have hsum : ∑ w : zigzagE8Graph.neighborSet v, e8Weight k ((v :: (w : Fin 8) :: L : List _) :
      Cycle (Fin 8)) = (((e8Neighbors v).map fun w => e8ListWeight (v :: w :: L)).sum : ℤ) := by
    have hmem (w : Fin 8) :
        w ∈ (e8Neighbors v).toFinset ↔ w ∈ zigzagE8Graph.neighborSet v := by
      rw [List.mem_toFinset, SimpleGraph.mem_neighborSet, zigzagE8Graph_adj_iff_mem_e8Neighbors]
    refine (Finset.sum_subtype _ hmem
      fun w => e8Weight k ((v :: w :: L : List _) : Cycle (Fin 8))).symm.trans ?_
    rw [List.sum_toFinset _ (nodup_e8Neighbors v)]
    simp [e8Weight_coe, Function.comp_def]
  rw [hsum]
  by_cases hlen : L.length = 8
  · -- A closed walk of length eight: apply the finite check.
    have hmem : L ++ [v] ∈ e8Walks 8 v := by
      refine mem_e8Walks 8 v _ (by simp [hlen]) ?_ hL
      cases L with
      | nil => rfl
      | cons a L => simpa using hv a rfl
    have hcheck := List.all_eq_true.mp
      (List.all_eq_true.mp e8ListWeight_relations v (List.mem_finRange v)) _ hmem
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, bne_self_eq_false,
      List.dropLast_concat, Bool.false_or, beq_iff_eq] at hcheck
    obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero hcheck
    rw [hm, Int.cast_mul, Int.cast_ofNat, h5, zero_mul]
  · -- Otherwise every term has length different from ten.
    have hzero (w : Fin 8) : e8ListWeight (v :: w :: L) = 0 := by
      simp only [e8ListWeight, List.length_cons]
      exact ite_eq_right (by omega)
    simp [hzero]

/-! ### The cyclic class -/

local notation "Q" => DoubledQuiver zigzagE8Graph
local notation "Π" => signlessPreprojectiveAlgebra k Q

/-- The closed walk `y z⁴` at the branch node of `E₈` is homogeneous of path degree ten. -/
theorem signlessWord_E8_cyclicWord_mem_grade_ten :
    signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3] ∈
      signlessPreprojectiveGrade k Q 10 := by
  obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k (G := zigzagE8Graph) 3
    [2, 3, 4, 3, 4, 3, 4, 3, 4, 3] (by decide)
  rw [← hp]
  apply signlessPreprojectiveMk_mem_grade
  apply ofPath_mem_grade_of_length
  have hh := congrArg List.length hv
  simp only [Path.vertices_length, List.length_map, List.length_reverse, List.length_cons,
    List.length_nil] at hh
  exact (by omega : p.length = 10)

/-- **In characteristic five, the closed walk `y z⁴` of degree ten is not a sum of commutators**
in the signless preprojective algebra of `E₈`. -/
theorem signlessWord_E8_cyclicWord_notMem_commutatorSubmodule [Nontrivial k] (h5 : (5 : k) = 0) :
    signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3] ∉ commutatorSubmodule k Π := by
  intro h
  have h₀ := LinearMap.mem_ker.mp (commutatorSubmodule_le_ker_signlessNecklaceFunctional
    (isSignlessNecklaceWeight_e8Weight k h5) h)
  have hw : e8ListWeight [3, 4, 3, 4, 3, 4, 3, 4, 3, 2] = 1 := by decide
  rw [signlessNecklaceFunctional_signlessWord _ _ _ (by decide) (by decide), List.reverse_cons,
    e8Weight_coe] at h₀
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    hw, Int.cast_one] at h₀
  exact one_ne_zero h₀

/-- In characteristic five, the class of the closed walk `y z⁴` in the cyclic quotient of the
signless preprojective algebra of `E₈` is nonzero. -/
theorem mkQ_signlessWord_E8_cyclicWord_ne_zero [Nontrivial k] (h5 : (5 : k) = 0) :
    (commutatorSubmodule k Π).mkQ (signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3])
      ≠ 0 := by
  intro h
  exact signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k h5
    ((Submodule.Quotient.mk_eq_zero _).mp h)

/-- **In characteristic five, the preprojective algebra of every orientation of `E₈` has a
degree-ten element which is not a sum of commutators.** -/
theorem exists_mem_preprojectiveGrade_E8_ten_notMem_commutatorSubmodule [Nontrivial k]
    (h5 : (5 : k) = 0) (o : Orientation zigzagE8Graph) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph o),
      z ∈ preprojectiveGrade k (OrientedQuiver zigzagE8Graph o) 10 ∧
        z ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph o)) := by
  let E := zigzagE8Coloring.signlessPreprojectiveAlgebraEquiv k o
  refine ⟨E (signlessWord k zigzagE8Graph [3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3]),
    zigzagE8Coloring.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o
      (signlessWord_E8_cyclicWord_mem_grade_ten k), fun h => ?_⟩
  apply signlessWord_E8_cyclicWord_notMem_commutatorSubmodule k h5
  simpa only [AlgEquiv.symm_apply_apply] using map_mem_commutatorSubmodule E.symm h

end TauCeti
