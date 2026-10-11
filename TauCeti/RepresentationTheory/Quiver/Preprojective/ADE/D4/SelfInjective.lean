/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.Basic

/-!
# The preprojective algebra of `D₄` is Frobenius and self-injective

In the Bourbaki labelling of `D₄` the vertex `1` is trivalent and `0, 2, 3` are leaves. A walk in
the doubled quiver is recorded as the list of its vertices, **latest vertex first**, so that
prepending a vertex is left multiplication by an arrow in Tau Ceti's later-factor-first
convention; `TauCeti.signlessWord` sends such a list to its class in the signless preprojective
algebra `Π` of `D₄`.

This file exhibits an explicit basis of `Π` by `28` walk classes and a Frobenius functional on it.
Order the leaves cyclically as `0 → 2 → 3 → 0`. A closed walk of length four visits two leaves, in
order, and the functional `TauCeti.signlessPreprojectiveD4FrobeniusFunctional` takes its class to
`1` if the second leaf follows the first in this cyclic order, to `-1` if it precedes it, and to
`0` if the two leaves agree; it vanishes on walks of every other length. On the path algebra this
functional kills every product `a ρ_v b` with a signless relator `ρ_v`, so it descends to `Π`.

The basis consists of the vertex idempotents, the six arrows, eight paths of length two, six paths
of length three and one closed path of length four at each vertex. Every path class reduces to a
combination of these by the leaf relations `l → 1 → l = 0` and the relation
`∑_l (1 → l → 1) = 0` at the trivalent vertex, together with the vanishing of paths of length five
from `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.Basic`. The Gram matrix of
`(x, y) ↦ φ (x * y)` on the basis is a signed permutation matrix, which proves at once that the
`28` classes are linearly independent and that `φ` is a Frobenius functional, over every
commutative ring. Hence the signless algebra of `D₄` has dimension `28` and, over every field,
characteristic two included, it is left and right self-injective. Since `D₄` is bipartite, its
signless algebra is the preprojective algebra of each orientation of `D₄` up to a sign rescaling
of the arrows, so these preprojective algebras are self-injective as well.

## Main definitions

* `TauCeti.signlessPreprojectiveD4BasisWalks`: the `28` walks of the basis.
* `TauCeti.signlessPreprojectiveD4Basis`: the basis of the signless algebra of `D₄` by their
  classes.
* `TauCeti.signlessPreprojectiveD4FrobeniusFunctional`: the Frobenius functional.
* `TauCeti.signlessPreprojectiveD4LeafSign` and `TauCeti.signlessPreprojectiveD4SocleSign`: the
  signs comparing two leaves, and the values of the functional on walks of length four.

## Main results

* `TauCeti.finrank_signlessPreprojectiveAlgebra_D4`: the signless algebra of `D₄` has dimension
  `28`.
* `TauCeti.isFrobeniusFunctional_signlessPreprojectiveD4FrobeniusFunctional`: the functional is a
  Frobenius functional.
* `TauCeti.moduleInjective_signlessPreprojectiveAlgebra_D4` and
  `TauCeti.moduleInjective_op_signlessPreprojectiveAlgebra_D4`: the signless algebra of `D₄` is
  left and right self-injective.
* `TauCeti.moduleInjective_preprojectiveAlgebra_D4` and
  `TauCeti.moduleInjective_op_preprojectiveAlgebra_D4`: the preprojective algebra of every
  orientation of `D₄` is left and right self-injective.

## Implementation notes

The finitely many combinatorial facts about walks — compatibility of the socle signs with the
relations, the shape of the Gram matrix, and which one-step extensions of basis walks need a
reduction — are checked by `decide` on lists of vertices. Only the reductions themselves are
carried out in `Π`.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra and its local relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the Frobenius property of the
  preprojective algebras of finite Dynkin type.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

-- The finiteness structure on the neighbourhoods under which the `D₄` algebras of
-- `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.D4.Basic` are stated.
attribute [local instance] d4NeighborSetFintype

/-! ### Walks and their signs -/

/-- The sign comparing two leaves `a, b` of `D₄` in the cyclic order `0 → 2 → 3 → 0`: it is `1`
if `b` follows `a`, `-1` if `b` precedes `a`, and `0` if `a = b` or one of them is the trivalent
vertex `1`. -/
def signlessPreprojectiveD4LeafSign (a b : Fin 4) : ℤ :=
  ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 0, 0, 1], ![1, 0, -1, 0]] a b

/-- The **socle sign** of a list of five vertices of `D₄`, read as a walk of length four from its
first vertex. A closed walk `a → 1 → b → 1 → a` from a leaf, or `1 → a → 1 → b → 1` from the
trivalent vertex, visits the leaves `a` and then `b`, and its sign compares them in the cyclic
order `0 → 2 → 3 → 0` of the leaves. Every other list has sign `0`. -/
def signlessPreprojectiveD4SocleSign : List (Fin 4) → ℤ
  | [x₀, x₁, x₂, x₃, x₄] =>
    if x₁ = 1 ∧ x₃ = 1 ∧ x₀ = x₄ then signlessPreprojectiveD4LeafSign x₀ x₂
    else if x₀ = 1 ∧ x₂ = 1 ∧ x₄ = 1 then signlessPreprojectiveD4LeafSign x₁ x₃ else 0
  | _ => 0

/-- Only lists of length five have a nonzero socle sign. -/
@[simp]
theorem signlessPreprojectiveD4SocleSign_of_length_ne {l : List (Fin 4)} (hl : l.length ≠ 5) :
    signlessPreprojectiveD4SocleSign l = 0 := by
  match l, hl with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], h => exact absurd rfl h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _ => rfl

/-- The leaf sign is antisymmetric. -/
theorem signlessPreprojectiveD4LeafSign_swap (a b : Fin 4) :
    signlessPreprojectiveD4LeafSign b a = -signlessPreprojectiveD4LeafSign a b := by
  revert a b
  decide

/-- A leaf compared with itself has sign `0`. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_self (a : Fin 4) :
    signlessPreprojectiveD4LeafSign a a = 0 := by
  revert a
  decide

/-- The trivalent vertex `1` has sign `0` against every vertex. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_one_left (b : Fin 4) :
    signlessPreprojectiveD4LeafSign 1 b = 0 := by
  revert b
  decide

/-- Every vertex has sign `0` against the trivalent vertex `1`. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_one_right (a : Fin 4) :
    signlessPreprojectiveD4LeafSign a 1 = 0 := by
  revert a
  decide

/-- The leaf `2` follows the leaf `0` in the cyclic order. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_zero_two : signlessPreprojectiveD4LeafSign 0 2 = 1 := by
  decide

/-- The leaf `3` follows the leaf `2` in the cyclic order. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_two_three : signlessPreprojectiveD4LeafSign 2 3 = 1 := by
  decide

/-- The leaf `0` follows the leaf `3` in the cyclic order. -/
@[simp]
theorem signlessPreprojectiveD4LeafSign_three_zero : signlessPreprojectiveD4LeafSign 3 0 = 1 := by
  decide

/-- The socle sign of a list of five vertices. -/
theorem signlessPreprojectiveD4SocleSign_five (x₀ x₁ x₂ x₃ x₄ : Fin 4) :
    signlessPreprojectiveD4SocleSign [x₀, x₁, x₂, x₃, x₄] =
      if x₁ = 1 ∧ x₃ = 1 ∧ x₀ = x₄ then signlessPreprojectiveD4LeafSign x₀ x₂
      else if x₀ = 1 ∧ x₂ = 1 ∧ x₄ = 1 then signlessPreprojectiveD4LeafSign x₁ x₃ else 0 := by
  rw [signlessPreprojectiveD4SocleSign]

/-- A closed walk `a → 1 → b → 1 → a` has the sign comparing `a` with `b`. -/
@[simp]
theorem signlessPreprojectiveD4SocleSign_leaf (a b : Fin 4) :
    signlessPreprojectiveD4SocleSign [a, 1, b, 1, a] = signlessPreprojectiveD4LeafSign a b := by
  revert a b
  decide

/-- A closed walk `1 → a → 1 → b → 1` has the sign comparing `a` with `b`. -/
@[simp]
theorem signlessPreprojectiveD4SocleSign_trivalent (a b : Fin 4) :
    signlessPreprojectiveD4SocleSign [1, a, 1, b, 1] = signlessPreprojectiveD4LeafSign a b := by
  revert a b
  decide

/-- The socle signs are compatible with the signless relations: inserting the backtracks
`i → w → i` at any position and summing over the neighbours `w` of `i` gives `0`. -/
private theorem sum_signlessPreprojectiveD4SocleSign_backtrack (Y X : List (Fin 4)) (i : Fin 4) :
    ∑ w ∈ Finset.univ.filter (zigzagD4Graph.Adj i),
      signlessPreprojectiveD4SocleSign (Y ++ i :: w :: i :: X) = 0 := by
  by_cases hl : Y.length + X.length = 2
  · rcases Y with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, Y⟩⟩⟩ <;>
      rcases X with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, X⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons] at hl <;> try omega
    all_goals decide +revert
  · exact Finset.sum_eq_zero fun w _ =>
      signlessPreprojectiveD4SocleSign_of_length_ne (by simp; omega)

section CommRing

variable (k : Type*) [CommRing k]

local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver zigzagD4Graph)
local notation "A" => signlessArrow k zigzagD4Graph
local notation "W" => signlessWord k zigzagD4Graph

/-! ### Walks of length five -/

/-- **Walks of length at least five vanish** in the signless algebra of `D₄`. -/
theorem signlessWord_D4_eq_zero_of_six_le_length {l : List (Fin 4)}
    (hl : 6 ≤ l.length) : W l = 0 := by
  by_cases hw : l.IsChain zigzagD4Graph.Adj
  · obtain ⟨i, r, rfl⟩ : ∃ i r, l = i :: r := by
      cases l with
      | nil => simp at hl
      | cons i r => exact ⟨i, r, rfl⟩
    obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k i r hw
    rw [← hp]
    apply signlessPreprojectiveMk_D4_ofPath_eq_zero_of_five_le
    have h := congrArg List.length hv
    rw [Path.vertices_length, List.length_map, List.length_reverse] at h
    dsimp only
    omega
  · exact signlessWord_eq_zero_of_not_isChain k hw

/-! ### The Frobenius functional -/

/-- The socle-sign functional on the path algebra of the doubled `D₄` quiver, which reads a path
through its vertex list. It descends to `TauCeti.signlessPreprojectiveD4FrobeniusFunctional`. -/
private noncomputable def d4SocleFunctionalAux :
    pathAlgebra k (DoubledQuiver zigzagD4Graph) →ₗ[k] k :=
  liftLinear k fun x =>
    (signlessPreprojectiveD4SocleSign (x.2.2.vertices.map (vertexEquiv zigzagD4Graph).symm) : k)

private theorem d4SocleFunctionalAux_ofPath (x : Quiver.TotalPath (DoubledQuiver zigzagD4Graph)) :
    d4SocleFunctionalAux k (ofPath x) =
      signlessPreprojectiveD4SocleSign (x.2.2.vertices.map (vertexEquiv zigzagD4Graph).symm) := by
  rw [d4SocleFunctionalAux, liftLinear_ofPath]

private theorem d4SocleFunctionalAux_ofPath_mul_relator_mul_ofPath (i : Fin 4)
    [Fintype (Quiver.Star (vertex zigzagD4Graph i))]
    (x y : Quiver.TotalPath (DoubledQuiver zigzagD4Graph)) :
    d4SocleFunctionalAux k (ofPath x * signlessPreprojectiveRelator k (vertex zigzagD4Graph i) *
      ofPath y) = 0 := by
  rw [signlessPreprojectiveRelator_congr k _ _ (instFintypeStarVertex zigzagD4Graph i),
    signlessPreprojectiveRelator_vertex,
    Finset.mul_sum, Finset.sum_mul, map_sum]
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases ha : a = vertex zigzagD4Graph i
  swap
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_not_composable (Ne.symm ha), zero_mul,
      map_zero]
  subst a
  by_cases hd : d = vertex zigzagD4Graph i
  swap
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [backtrackElem_eq_ofPath, mul_assoc, ofPath_mul_ofPath_of_not_composable hd, mul_zero,
      map_zero]
  subst d
  -- The product is the path `q`, then a backtrack `i → w → i`, then `p`.
  have hp : p.vertices = vertex zigzagD4Graph i :: p.vertices.tail :=
    (List.cons_head_tail p.vertices_ne_nil).symm.trans (by rw [Path.vertices_head_eq])
  simp only [backtrackElem_eq_ofPath, ofPath_mul_ofPath_of_comp, d4SocleFunctionalAux_ofPath,
    Path.vertices_comp, backtrackPath_eq_comp, arrowPath_eq_toPath, Path.vertices_toPath]
  rw [hp]
  simp only [List.map_append, List.map_cons, vertexEquiv_symm_vertex, List.dropLast_cons_cons,
    List.dropLast_singleton, List.cons_append, List.nil_append]
  have h := sum_signlessPreprojectiveD4SocleSign_backtrack
    (q.vertices.dropLast.map (vertexEquiv zigzagD4Graph).symm)
    (p.vertices.tail.map (vertexEquiv zigzagD4Graph).symm) i
  rw [Finset.sum_subtype _ (p := (· ∈ zigzagD4Graph.neighborSet i)) (fun w => by simp)] at h
  rw [← Int.cast_sum, h, Int.cast_zero]

private theorem d4SocleFunctionalAux_mul_relator_mul (i : Fin 4)
    [Fintype (Quiver.Star (vertex zigzagD4Graph i))]
    (a b : pathAlgebra k (DoubledQuiver zigzagD4Graph)) :
    d4SocleFunctionalAux k (a * signlessPreprojectiveRelator k (vertex zigzagD4Graph i) * b) =
      0 := by
  induction a using induction_linear with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, add_mul, map_add, ha, ha', add_zero]
  | single x c =>
    induction b using induction_linear with
    | zero => simp
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', add_zero]
    | single y d =>
      rw [single_eq_smul_ofPath, single_eq_smul_ofPath, smul_mul_assoc, smul_mul_assoc,
        mul_smul_comm, map_smul, map_smul, d4SocleFunctionalAux_ofPath_mul_relator_mul_ofPath,
        smul_zero, smul_zero]

private theorem d4SocleFunctionalAux_eq_zero {x : pathAlgebra k (DoubledQuiver zigzagD4Graph)}
    (hx : π x = 0) : d4SocleFunctionalAux k x = 0 := by
  rw [signlessPreprojectiveMk_eq_zero_iff, signlessPreprojectiveIdeal_eq_span] at hx
  suffices h : ∀ a b, d4SocleFunctionalAux k (a * x * b) = 0 by simpa using h 1 1
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := exists_eq_vertex zigzagD4Graph v
    exact fun a b => by convert d4SocleFunctionalAux_mul_relator_mul k i a b
  | zero => simp
  | add x y _ _ hx hy => intro a b; rw [mul_add, add_mul, map_add, hx, hy, add_zero]
  | neg x _ hx => intro a b; rw [mul_neg, neg_mul, map_neg, hx, neg_zero]
  | left_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx (a * c) b
  | right_absorb c x _ hx => intro a b; simpa only [mul_assoc] using hx a (c * b)

/-- **The Frobenius functional on the signless algebra of `D₄`.** It takes the class of a closed
walk of length four to its socle sign `TauCeti.signlessPreprojectiveD4SocleSign`, comparing the
two leaves it visits in the cyclic order `0 → 2 → 3 → 0`, and vanishes on the classes of all
walks of other lengths. -/
noncomputable def signlessPreprojectiveD4FrobeniusFunctional : Π →ₗ[k] k :=
  (LinearMap.ker (π).toLinearMap).liftQ (d4SocleFunctionalAux k)
      (fun _ hx =>
        LinearMap.mem_ker.mpr (d4SocleFunctionalAux_eq_zero k (LinearMap.mem_ker.mp hx))) ∘ₗ
    ((π).toLinearMap.quotKerEquivOfSurjective
      (signlessPreprojectiveMk_surjective k _)).symm.toLinearMap

local notation "φ" => signlessPreprojectiveD4FrobeniusFunctional k

private theorem signlessPreprojectiveD4FrobeniusFunctional_mk_ofPath
    (x : Quiver.TotalPath (DoubledQuiver zigzagD4Graph)) :
    φ (π (ofPath x)) =
      signlessPreprojectiveD4SocleSign (x.2.2.vertices.map (vertexEquiv zigzagD4Graph).symm) := by
  have h := (π).toLinearMap.quotKerEquivOfSurjective_symm_apply
    (signlessPreprojectiveMk_surjective k _) (ofPath x)
  rw [AlgHom.toLinearMap_apply] at h
  rw [signlessPreprojectiveD4FrobeniusFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
    Submodule.liftQ_apply, d4SocleFunctionalAux_ofPath]

/-- The Frobenius functional takes the class of a walk to the socle sign of its vertices, read
from the first vertex. -/
theorem signlessPreprojectiveD4FrobeniusFunctional_signlessWord (l : List (Fin 4))
    (hl : l.IsChain zigzagD4Graph.Adj) (hne : l ≠ []) :
    φ (W l) = signlessPreprojectiveD4SocleSign l.reverse := by
  obtain ⟨i, r, rfl⟩ : ∃ i r, l = i :: r := by
    cases l with
    | nil => exact absurd rfl hne
    | cons i r => exact ⟨i, r, rfl⟩
  obtain ⟨a, p, hp, hv⟩ := exists_ofPath_eq_signlessWord k i r hl
  rw [← hp, signlessPreprojectiveD4FrobeniusFunctional_mk_ofPath]
  simp only [hv, List.map_map]
  simp [Function.comp_def, vertexEquiv_symm_vertex]

/-! ### The basis walks and the Gram matrix -/

/-- The `28` walks whose classes form a basis of the signless algebra of `D₄`, latest vertex
first: the four vertices, the six arrows, six paths of length two between distinct leaves, two of
the three backtracks at the trivalent vertex, six paths of length three and one closed path of
length four at each vertex. -/
def signlessPreprojectiveD4BasisWalks : Finset (List (Fin 4)) :=
  {[0], [1], [2], [3], [1, 0], [1, 2], [1, 3], [0, 1], [2, 1], [3, 1],
    [2, 1, 0], [3, 1, 0], [0, 1, 2], [3, 1, 2], [0, 1, 3], [2, 1, 3], [1, 0, 1], [1, 2, 1],
    [1, 2, 1, 0], [1, 3, 1, 2], [1, 0, 1, 3], [0, 1, 2, 1], [2, 1, 0, 1], [3, 1, 0, 1],
    [0, 1, 2, 1, 0], [2, 1, 3, 1, 2], [3, 1, 0, 1, 3], [1, 2, 1, 0, 1]}

local notation "T" => signlessPreprojectiveD4BasisWalks

/-- The Gram matrix of the Frobenius pairing on the basis walks, computed combinatorially: the
socle sign of the concatenated walk, or `0` if the two walks do not meet. -/
private def d4Gram (s t : List (Fin 4)) : ℤ :=
  if s.getLast? = t.head? then signlessPreprojectiveD4SocleSign (s.dropLast ++ t).reverse else 0

private theorem isChain_of_mem_signlessPreprojectiveD4BasisWalks :
    ∀ t ∈ T, t ≠ [] ∧ t.IsChain zigzagD4Graph.Adj := by
  decide

private theorem isChain_append_of_mem_signlessPreprojectiveD4BasisWalks :
    ∀ s ∈ T, ∀ t ∈ T, s.getLast? = t.head? → (s.dropLast ++ t).IsChain zigzagD4Graph.Adj := by
  decide

/-- Every column of the Gram matrix has exactly one nonzero entry. -/
private theorem existsUnique_d4Gram_ne_zero_left :
    ∀ u ∈ T, ∃ t ∈ T, d4Gram t u ≠ 0 ∧ ∀ t' ∈ T, d4Gram t' u ≠ 0 → t' = t := by
  decide

/-- Every row of the Gram matrix has exactly one nonzero entry. -/
private theorem existsUnique_d4Gram_ne_zero_right :
    ∀ t ∈ T, ∃ u ∈ T, d4Gram t u ≠ 0 ∧ ∀ u' ∈ T, d4Gram t u' ≠ 0 → u' = u := by
  decide

/-- The nonzero entries of the Gram matrix are signs. -/
private theorem d4Gram_mul_self :
    ∀ t ∈ T, ∀ u ∈ T, d4Gram t u ≠ 0 → d4Gram t u * d4Gram t u = 1 := by
  decide

/-- On two basis walks, the Frobenius pairing is the combinatorial Gram matrix. -/
private theorem signlessPreprojectiveD4FrobeniusFunctional_mul {s t : List (Fin 4)} (hs : s ∈ T)
    (ht : t ∈ T) : φ (W s * W t) = d4Gram s t := by
  obtain ⟨hs₀, -⟩ := isChain_of_mem_signlessPreprojectiveD4BasisWalks s hs
  obtain ⟨j, t, rfl⟩ : ∃ j t', t = j :: t' := by
    cases t with
    | nil => exact absurd ht (by decide)
    | cons j t => exact ⟨j, t, rfl⟩
  have hlast := List.getLast?_eq_some_getLast hs₀
  rw [signlessWord_mul_signlessWord k s hs₀, d4Gram, hlast,
    List.head?_cons]
  by_cases h : s.getLast hs₀ = j
  · rw [ite_eq_left h, ite_eq_left (congrArg some h)]
    exact signlessPreprojectiveD4FrobeniusFunctional_signlessWord k _
      (isChain_append_of_mem_signlessPreprojectiveD4BasisWalks s hs _ ht
        (by rw [hlast, h, List.head?_cons])) (by simp)
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Option.some.inj h')), map_zero, Int.cast_zero]

/-- A combination of the rows of the Gram matrix which vanishes in every column is trivial. -/
private theorem eq_zero_of_forall_sum_mul_d4Gram {c : T → k}
    (hc : ∀ u : T, ∑ t : T, c t * d4Gram t u = 0) (t : T) : c t = 0 := by
  obtain ⟨u, hu, htu, -⟩ := existsUnique_d4Gram_ne_zero_right t.1 t.2
  obtain ⟨t', ht', -, huniq⟩ := existsUnique_d4Gram_ne_zero_left u hu
  have ht : t = ⟨t', ht'⟩ := Subtype.ext (huniq t t.2 htu)
  -- Only the row `t` contributes to the column `u`.
  have hzero (t'' : T) (ht'' : t'' ≠ t) : d4Gram t'' u = 0 := by
    by_contra h0
    exact ht'' (Subtype.ext ((huniq _ t''.2 h0).trans (congrArg Subtype.val ht).symm))
  have h := hc ⟨u, hu⟩
  rw [Finset.sum_eq_single t (fun t'' _ ht'' => by rw [hzero t'' ht'', Int.cast_zero, mul_zero])
    (by simp)] at h
  have hsq := congrArg (Int.cast : ℤ → k) (d4Gram_mul_self t t.2 u hu htu)
  rw [Int.cast_mul, Int.cast_one] at hsq
  rw [← mul_one (c t), ← hsq, ← mul_assoc, h, zero_mul]

/-- A combination of the columns of the Gram matrix which vanishes in every row is trivial. -/
private theorem eq_zero_of_forall_sum_d4Gram_mul {c : T → k}
    (hc : ∀ s : T, ∑ u : T, d4Gram s u * c u = 0) (u : T) : c u = 0 := by
  obtain ⟨t, ht, htu, -⟩ := existsUnique_d4Gram_ne_zero_left u.1 u.2
  obtain ⟨u', hu', -, huniq⟩ := existsUnique_d4Gram_ne_zero_right t ht
  have hu : u = ⟨u', hu'⟩ := Subtype.ext (huniq u u.2 htu)
  -- Only the column `u` contributes to the row `t`.
  have hzero (u'' : T) (hu'' : u'' ≠ u) : d4Gram t u'' = 0 := by
    by_contra h0
    exact hu'' (Subtype.ext ((huniq _ u''.2 h0).trans (congrArg Subtype.val hu).symm))
  have h := hc ⟨t, ht⟩
  rw [Finset.sum_eq_single u (fun u'' _ hu'' => by rw [hzero u'' hu'', Int.cast_zero, zero_mul])
    (by simp)] at h
  have hsq := congrArg (Int.cast : ℤ → k) (d4Gram_mul_self t ht u u.2 htu)
  rw [Int.cast_mul, Int.cast_one] at hsq
  rw [← one_mul (c u), ← hsq, mul_assoc, h, mul_zero]

/-- **The classes of the basis walks are linearly independent** over every commutative ring. -/
theorem linearIndependent_signlessWord_D4 :
    LinearIndependent k (fun t : T => W t) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  refine eq_zero_of_forall_sum_mul_d4Gram k fun u => ?_
  have h := congrArg (fun x => φ (x * W u)) hc
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, zero_mul, map_zero,
    signlessPreprojectiveD4FrobeniusFunctional_mul k (Subtype.prop _) u.2, smul_eq_mul] at h
  exact h

/-! ### Spanning -/

local notation "S" => Submodule.span k (Set.range fun t : T => W t)

private theorem signlessArrow_d4_eq_zero {i j : Fin 4} (h : ¬ zigzagD4Graph.Adj i j) : A i j = 0 :=
  signlessArrow_eq_zero k fun _ _ h' => h (by simpa using h')

/-- At a leaf `l` of `D₄` the signless relation kills the backtrack `l → 1 → l`. -/
private theorem signlessArrow_d4_mul_signlessArrow_d4_leaf {l : Fin 4} (hl : l ≠ 1) :
    A (1 : Fin 4) l * A l (1 : Fin 4) = 0 := by
  have hleaf : ∀ w : Fin 4, w ≠ 1 → ¬ zigzagD4Graph.Adj l w := by
    revert l
    decide
  rw [← sum_signlessArrow_mul_signlessArrow k zigzagD4Graph l, Finset.sum_eq_single (1 : Fin 4)
    (fun w _ hw => by rw [signlessArrow_d4_eq_zero k (hleaf w hw), mul_zero]) (by simp)]

/-- A walk whose latest steps form a leaf backtrack `l → 1 → l`, possibly followed by more
steps, has class `0`. -/
private theorem signlessWord_D4_backtrack (X : List (Fin 4)) {l : Fin 4} (hl : l ≠ 1)
    (r : List (Fin 4)) : W (X ++ l :: 1 :: l :: r) = 0 := by
  induction X with
  | nil =>
    rw [List.nil_append, signlessWord_cons_cons,
      signlessWord_cons_cons, ← mul_assoc,
      signlessArrow_d4_mul_signlessArrow_d4_leaf k hl, zero_mul]
  | cons x X ih =>
    obtain ⟨i, hi⟩ : ∃ i, (X ++ l :: 1 :: l :: r).head? = some i := by
      cases X with
      | nil => exact ⟨l, rfl⟩
      | cons y X => exact ⟨y, rfl⟩
    rw [List.cons_append, signlessWord_cons k hi, ih, mul_zero]

private theorem signlessWord_D4_backtrack_mem (X : List (Fin 4)) {l : Fin 4}
    (hl : l ≠ 1) (r : List (Fin 4)) : W (X ++ l :: 1 :: l :: r) ∈ S := by
  rw [signlessWord_D4_backtrack k X hl r]
  exact zero_mem _

/-- The relation at the trivalent vertex, inserted at any position of a walk. -/
private theorem signlessWord_D4_center (X r : List (Fin 4)) :
    W (X ++ 1 :: 0 :: 1 :: r) + W (X ++ 1 :: 2 :: 1 :: r) + W (X ++ 1 :: 3 :: 1 :: r) = 0 := by
  induction X with
  | nil =>
    have hrel := sum_signlessArrow_mul_signlessArrow k zigzagD4Graph 1
    simp only [Fin.sum_univ_four, Fin.isValue] at hrel
    rw [signlessArrow_d4_eq_zero k (i := 1) (j := 1) (by decide), zero_mul, add_zero] at hrel
    simp only [List.nil_append, signlessWord_cons_cons, ← mul_assoc, ← add_mul]
    rw [hrel, zero_mul]
  | cons x X ih =>
    obtain ⟨i, hi⟩ : ∃ i, ∀ a, (X ++ 1 :: a :: 1 :: r).head? = some i := by
      cases X with
      | nil => exact ⟨1, fun _ => rfl⟩
      | cons y X => exact ⟨y, fun _ => rfl⟩
    simp only [List.cons_append]
    rw [signlessWord_cons k (hi 0), signlessWord_cons k (hi 2),
      signlessWord_cons k (hi 3), ← mul_add, ← mul_add, ih, mul_zero]

private theorem signlessWord_D4_center_mem₀ (X r : List (Fin 4))
    (h₂ : W (X ++ 1 :: 2 :: 1 :: r) ∈ S) (h₃ : W (X ++ 1 :: 3 :: 1 :: r) ∈ S) :
    W (X ++ 1 :: 0 :: 1 :: r) ∈ S := by
  have h := signlessWord_D4_center k X r
  rw [add_assoc] at h
  rw [eq_neg_of_add_eq_zero_left h]
  exact neg_mem (add_mem h₂ h₃)

private theorem signlessWord_D4_center_mem₂ (X r : List (Fin 4))
    (h₀ : W (X ++ 1 :: 0 :: 1 :: r) ∈ S) (h₃ : W (X ++ 1 :: 3 :: 1 :: r) ∈ S) :
    W (X ++ 1 :: 2 :: 1 :: r) ∈ S := by
  have h := signlessWord_D4_center k X r
  rw [add_comm (W (X ++ 1 :: 0 :: 1 :: r)), add_assoc] at h
  rw [eq_neg_of_add_eq_zero_left h]
  exact neg_mem (add_mem h₀ h₃)

private theorem signlessWord_D4_center_mem₃ (X r : List (Fin 4))
    (h₀ : W (X ++ 1 :: 0 :: 1 :: r) ∈ S) (h₂ : W (X ++ 1 :: 2 :: 1 :: r) ∈ S) :
    W (X ++ 1 :: 3 :: 1 :: r) ∈ S := by
  rw [eq_neg_of_add_eq_zero_right (signlessWord_D4_center k X r)]
  exact neg_mem (add_mem h₀ h₂)

private theorem signlessWord_D4_mem_of_mem {w : List (Fin 4)} (hw : w ∈ T) : W w ∈ S :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

/-- The walks of length at most four which extend a basis walk by one arrow without being basis
walks themselves. -/
private def d4ReducedWalks : Finset (List (Fin 4)) :=
  {[0, 1, 0], [2, 1, 2], [3, 1, 3], [1, 3, 1], [1, 3, 1, 0], [1, 0, 1, 2], [1, 2, 1, 3],
    [0, 1, 0, 1], [2, 1, 2, 1], [3, 1, 2, 1], [2, 1, 2, 1, 0], [3, 1, 2, 1, 0], [0, 1, 3, 1, 2],
    [3, 1, 3, 1, 2], [0, 1, 0, 1, 3], [2, 1, 0, 1, 3], [1, 0, 1, 2, 1], [1, 3, 1, 0, 1]}

/-- Extending a basis walk by one vertex gives a basis walk, a list which is not a walk, a walk of
length five, or one of `d4ReducedWalks`. -/
private theorem cons_mem_signlessPreprojectiveD4BasisWalks_or :
    ∀ t ∈ T, ∀ j : Fin 4, j :: t ∈ T ∨ ¬ (j :: t).IsChain zigzagD4Graph.Adj ∨
      6 ≤ (j :: t).length ∨ j :: t ∈ d4ReducedWalks := by
  decide

private theorem signlessWord_D4_mem_of_mem_d4ReducedWalks {w : List (Fin 4)}
    (hw : w ∈ d4ReducedWalks) : W w ∈ S := by
  have hT {w : List (Fin 4)} (hw : w ∈ T := by decide) : W w ∈ S :=
    signlessWord_D4_mem_of_mem k hw
  have hZ (X : List (Fin 4)) (l : Fin 4) (r : List (Fin 4)) (hl : l ≠ 1 := by decide) :=
    signlessWord_D4_backtrack_mem k X hl r
  -- Two closed walks of length four at the trivalent vertex, used as intermediate steps.
  have h₁ : W [1, 3, 1, 0, 1] ∈ S :=
    signlessWord_D4_center_mem₃ k [] [0, 1] (hZ [1] 0 [1]) hT
  have h₂ : W [1, 3, 1, 2, 1] ∈ S :=
    signlessWord_D4_center_mem₂ k [1, 3] [] h₁ (hZ [1] 3 [1])
  simp only [d4ReducedWalks, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact hZ [] 0 []
  · exact hZ [] 2 []
  · exact hZ [] 3 []
  · exact signlessWord_D4_center_mem₃ k [] [] hT hT
  · exact signlessWord_D4_center_mem₃ k [] [0] (hZ [1] 0 []) hT
  · exact signlessWord_D4_center_mem₀ k [] [2] (hZ [1] 2 []) hT
  · exact signlessWord_D4_center_mem₂ k [] [3] hT (hZ [1] 3 [])
  · exact hZ [] 0 [1]
  · exact hZ [] 2 [1]
  · exact signlessWord_D4_center_mem₂ k [3] [] hT (hZ [] 3 [1])
  · exact hZ [] 2 [1, 0]
  · exact signlessWord_D4_center_mem₂ k [3] [0] (hZ [3, 1] 0 []) (hZ [] 3 [1, 0])
  · exact signlessWord_D4_center_mem₃ k [0] [2] (hZ [] 0 [1, 2]) (hZ [0, 1] 2 [])
  · exact hZ [] 3 [1, 2]
  · exact hZ [] 0 [1, 3]
  · exact signlessWord_D4_center_mem₀ k [2] [3] (hZ [] 2 [1, 3]) (hZ [2, 1] 3 [])
  · exact signlessWord_D4_center_mem₀ k [] [2, 1] (hZ [1] 2 [1]) h₂
  · exact h₁

private theorem signlessArrow_mul_mem_span (i j : Fin 4) {x : Π} (hx : x ∈ S) : A i j * x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨t, ht⟩, rfl⟩ := hx
    obtain ⟨hne, -⟩ := isChain_of_mem_signlessPreprojectiveD4BasisWalks t ht
    obtain ⟨i', r, rfl⟩ : ∃ i' r, t = i' :: r := by
      cases t with
      | nil => exact absurd rfl hne
      | cons i' r => exact ⟨i', r, rfl⟩
    rw [signlessArrow_mul_signlessWord]
    split_ifs
    · rcases cons_mem_signlessPreprojectiveD4BasisWalks_or _ ht j with h | h | h | h
      · exact signlessWord_D4_mem_of_mem k h
      · rw [signlessWord_eq_zero_of_not_isChain k h]
        exact zero_mem _
      · rw [signlessWord_D4_eq_zero_of_six_le_length k h]
        exact zero_mem _
      · exact signlessWord_D4_mem_of_mem_d4ReducedWalks k h
    · exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **The classes of the basis walks span** the signless algebra of `D₄`. -/
theorem span_signlessWord_D4 : S = ⊤ := by
  have hpath (x : Quiver.TotalPath (DoubledQuiver zigzagD4Graph)) : π (ofPath x) ∈ S := by
    obtain ⟨a, b, p⟩ := x
    induction p with
    | nil =>
      obtain ⟨v, rfl⟩ := exists_eq_vertex zigzagD4Graph a
      rw [← vertexIdempotent_eq_ofPath, ← signlessWord_singleton]
      exact signlessWord_D4_mem_of_mem k (by fin_cases v <;> decide)
    | cons p e ih =>
      rw [← ofArrow_mul_ofPath, map_mul, signlessPreprojectiveMk_ofArrow_eq_signlessArrow]
      exact signlessArrow_mul_mem_span k _ _ ih
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  obtain ⟨f, rfl⟩ := signlessPreprojectiveMk_surjective k _ y
  induction f using induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single x c => rw [single_eq_smul_ofPath, map_smul]; exact Submodule.smul_mem _ c (hpath x)

/-! ### The basis and the Frobenius property -/

/-- **The basis of the signless algebra of `D₄`** by the classes of the `28` basis walks, over
every commutative ring. -/
noncomputable def signlessPreprojectiveD4Basis : Module.Basis T k Π :=
  .mk (linearIndependent_signlessWord_D4 k) (span_signlessWord_D4 k).ge

/-- The basis vector at a basis walk is the class of that walk. -/
@[simp]
theorem signlessPreprojectiveD4Basis_apply (t : T) : signlessPreprojectiveD4Basis k t = W t :=
  Module.Basis.mk_apply _ _ t

/-- **The signless algebra of `D₄` has dimension `28`.** -/
theorem finrank_signlessPreprojectiveAlgebra_D4 [Nontrivial k] : Module.finrank k Π = 28 := by
  rw [Module.finrank_eq_card_basis (signlessPreprojectiveD4Basis k), Fintype.card_coe]
  rfl

/-- **The signless algebra of `D₄` is Frobenius**: `(x, y) ↦ φ (x * y)` is nondegenerate on both
sides, over every commutative ring. -/
theorem isFrobeniusFunctional_signlessPreprojectiveD4FrobeniusFunctional :
    (φ).IsFrobeniusFunctional := by
  let b := signlessPreprojectiveD4Basis k
  -- The pairing of a combination of basis elements with a basis element.
  have hleft (x : Π) (u : T) : φ (x * W u) = ∑ t : T, b.repr x t * d4Gram t u := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul, b,
      signlessPreprojectiveD4Basis_apply,
      signlessPreprojectiveD4FrobeniusFunctional_mul k (Subtype.prop _) u.2]
  have hright (y : Π) (s : T) : φ (W s * y) = ∑ u : T, d4Gram s u * b.repr y u := by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, b,
      signlessPreprojectiveD4Basis_apply,
      signlessPreprojectiveD4FrobeniusFunctional_mul k s.2 (Subtype.prop _), mul_comm]
  refine LinearMap.isFrobeniusFunctional_iff.mpr ⟨fun x hx => ?_, fun y hy => ?_⟩
  · refine b.repr.injective (Finsupp.ext fun t => ?_)
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact eq_zero_of_forall_sum_mul_d4Gram k (fun u => (hleft x u).symm.trans (hx _)) t
  · refine b.repr.injective (Finsupp.ext fun u => ?_)
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact eq_zero_of_forall_sum_d4Gram_mul k (fun s => (hright y s).symm.trans (hy _)) u

end CommRing

section Field

variable (k : Type*) [Field k]

local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph)

/-- **The signless algebra of `D₄` is left self-injective** over every field. -/
theorem moduleInjective_signlessPreprojectiveAlgebra_D4 : Module.Injective Π Π :=
  (isFrobeniusFunctional_signlessPreprojectiveD4FrobeniusFunctional k).moduleInjective_self

/-- **The signless algebra of `D₄` is right self-injective** over every field. -/
theorem moduleInjective_op_signlessPreprojectiveAlgebra_D4 : Module.Injective Πᵐᵒᵖ Π :=
  (isFrobeniusFunctional_signlessPreprojectiveD4FrobeniusFunctional k).moduleInjective_op_self

/-! ### Every orientation of `D₄` -/

section Orientation

attribute [local instance] RingHomInvPair.of_ringEquiv

variable (o : Orientation zigzagD4Graph)

/-- The signless algebra of the bipartite `D₄` graph is the preprojective algebra of each of its
orientations, through the sign rescaling read from the two-colouring of `D₄`. -/
private noncomputable def d4SignlessEquivPreprojective :
    Π ≃ₐ[k] preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o) :=
  (orientationSignlessPreprojectiveAlgebraEquiv o k).trans
    (symmetrifySignlessPreprojectiveAlgebraEquiv k
      (c := fun i => zigzagD4Coloring ((OrientedQuiver.vertexEquiv _ o).symm i))
      fun _ _ a => zigzagD4Coloring.valid a.1)

/-- **The preprojective algebra of every orientation of `D₄` is left self-injective** over every
field. -/
theorem moduleInjective_preprojectiveAlgebra_D4 :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o))
      (preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o)) :=
  have := moduleInjective_signlessPreprojectiveAlgebra_D4 k
  .of_ringEquiv (d4SignlessEquivPreprojective k o).toRingEquiv
    (d4SignlessEquivPreprojective k o).toRingEquiv.toSemilinearEquiv

/-- **The preprojective algebra of every orientation of `D₄` is right self-injective** over
every field. -/
theorem moduleInjective_op_preprojectiveAlgebra_D4 :
    Module.Injective (preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o))ᵐᵒᵖ
      (preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o)) :=
  have := moduleInjective_op_signlessPreprojectiveAlgebra_D4 k
  .of_ringEquiv (RingEquiv.op (d4SignlessEquivPreprojective k o).toRingEquiv)
    { (d4SignlessEquivPreprojective k o).toRingEquiv.toAddEquiv with
      map_smul' := fun r x => by simp [MulOpposite.smul_eq_mul_unop] }

end Orientation

end Field

end TauCeti
