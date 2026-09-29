/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Preprojective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# The preprojective algebra of `D₄` is finite-dimensional

In the Bourbaki labelling of `D₄` the vertex `1` is trivalent and `0, 2, 3` are leaves, so every
path of the doubled quiver alternates between the trivalent vertex and the leaves. Write `u_l` for
the arrow `l → 1` and `d_l` for the arrow `1 → l`. In the signless algebra
`TauCeti.signlessPreprojectiveAlgebra` of the doubled graph, the relation at a leaf `l` is the
single backtrack `d_l u_l = 0`, and the relation at the trivalent vertex is
`u_0 d_0 + u_2 d_2 + u_3 d_3 = 0`. With only three leaves these relations force

```text
(u_a d_a) (u_b d_b) u_c = 0    and    d_c (u_b d_b) (u_a d_a) = 0
```

for all leaves `a, b, c`, and every path of length five is one of these two words. Hence **every
path of length at least five vanishes**. This is a computation with the relations alone; with a
fourth leaf, as in affine `D₄`, it fails, and the preprojective algebra is infinite-dimensional
(`TauCeti.AffineDynkinType.not_module_finite_preprojectiveAlgebra`).

The signless algebra of a bipartite graph is the preprojective algebra of each of its orientations,
by an explicit sign rescaling of the arrows. Thus the same bound holds in the preprojective algebra
`Π_k(Q)` of every orientation `Q` of `D₄`, over every commutative ring; the relation ideal is
admissible, and `Π_k(Q)` is finite-dimensional over every field. The bound five is `h - 1` for the
Coxeter number `h = 6` of `D₄`; that paths of length four survive is not proved here.

## Main results

* `TauCeti.signlessPreprojectiveMk_D4_ofPath_eq_zero_of_five_le`: paths of length at least five
  vanish in the signless algebra of `D₄`.
* `TauCeti.preprojectiveMk_D4_ofPath_eq_zero_of_five_le`: the same in the preprojective algebra of
  every orientation of `D₄`.
* `TauCeti.isAdmissibleIdeal_preprojectiveIdeal_D4`: the preprojective relation ideal of every
  orientation of `D₄` is admissible.
* `TauCeti.instFiniteDimensionalPreprojectiveAlgebraD4` and
  `TauCeti.instFiniteDimensionalSignlessPreprojectiveAlgebraD4`: the preprojective algebra of
  every orientation of `D₄`, and the signless algebra of `D₄`, are finite-dimensional.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective algebra and its local relations.
* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, for the
  signless relation and its comparison with the preprojective relation of a bipartite graph.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-! ### The relations of the doubled `D₄` quiver -/

/-- Every edge of the Bourbaki-labelled `D₄` graph joins the trivalent vertex `1` to a leaf. -/
private theorem zigzagD4Graph_adj_iff (i j : Fin 4) :
    zigzagD4Graph.Adj i j ↔ (i = 1 ∧ j ≠ 1) ∨ (i ≠ 1 ∧ j = 1) := by
  rw [zigzagD4Graph_adj]
  fin_cases i <;> fin_cases j <;> decide

/-- The neighbours of a vertex of `D₄` form a finite type; this is the finiteness structure of the
orientation comparisons of `TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective`. -/
noncomputable local instance d4NeighborSetFintype (i : Fin 4) :
    Fintype (zigzagD4Graph.neighborSet i) := Fintype.ofFinite _

section CommRing

variable (k : Type*) [CommRing k]

/-- The class of the doubled arrow from `i` to `j` in the signless algebra of `D₄`, or zero if `i`
and `j` are not adjacent. -/
private noncomputable def d4Arrow (i j : Fin 4) :
    signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph) :=
  if h : zigzagD4Graph.Adj i j then
    signlessPreprojectiveMk k _ (ofArrow (arrow zigzagD4Graph h))
  else 0

/-- The class of a doubled arrow between two named vertices of `D₄`. -/
private theorem signlessPreprojectiveMk_ofArrow_vertex {i j : Fin 4}
    (e : vertex zigzagD4Graph i ⟶ vertex zigzagD4Graph j) :
    signlessPreprojectiveMk k _ (ofArrow e) = d4Arrow k i j := by
  have h : zigzagD4Graph.Adj i j := (nonempty_hom_iff _).1 ⟨e⟩
  simp only [d4Arrow, h, ↓reduceDIte]
  exact congrArg (fun e => signlessPreprojectiveMk k _ (ofArrow e)) (Subsingleton.elim _ _)

/-- The class of an arbitrary doubled arrow of `D₄`. -/
private theorem signlessPreprojectiveMk_ofArrow {i j : DoubledQuiver zigzagD4Graph} (e : i ⟶ j) :
    signlessPreprojectiveMk k _ (ofArrow e) =
      d4Arrow k ((vertexEquiv zigzagD4Graph).symm i) ((vertexEquiv zigzagD4Graph).symm j) := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex _ i
  obtain ⟨j, rfl⟩ := exists_eq_vertex _ j
  rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex, signlessPreprojectiveMk_ofArrow_vertex]

/-- Between adjacent vertices, `d4Arrow` is the class of the doubled arrow. -/
private theorem d4Arrow_of_adj {i j : Fin 4} (h : zigzagD4Graph.Adj i j) :
    d4Arrow k i j = signlessPreprojectiveMk k _ (ofArrow (arrow zigzagD4Graph h)) := by
  simp only [d4Arrow, h, ↓reduceDIte]

/-- At a leaf `l` of `D₄` the signless relation kills the backtrack `l → 1 → l`. -/
private theorem d4Arrow_mul_d4Arrow_leaf {l : Fin 4} (h : zigzagD4Graph.Adj 1 l) :
    d4Arrow k 1 l * d4Arrow k l 1 = 0 := by
  have hsub : Subsingleton (zigzagD4Graph.neighborSet l) := ⟨fun w w' => Subtype.ext <| by
    have hw := (zigzagD4Graph_adj_iff _ _).1 w.2
    have hw' := (zigzagD4Graph_adj_iff _ _).1 w'.2
    have hl := (zigzagD4Graph_adj_iff _ _).1 h
    omega⟩
  have hrel := signlessPreprojectiveMk_signlessPreprojectiveRelator k (vertex zigzagD4Graph l)
  rw [signlessPreprojectiveRelator_congr k _ _ inferInstance,
    signlessPreprojectiveRelator_vertex, Fintype.sum_subsingleton _ ⟨1, h.symm⟩] at hrel
  rw [d4Arrow_of_adj k h, d4Arrow_of_adj k h.symm, ← map_mul]
  exact hrel ▸ congrArg (signlessPreprojectiveMk k _) (ofArrow_symm_mul_ofArrow _ k h.symm)

/-- At the trivalent vertex `1` of `D₄` the three backtracks `1 → l → 1` sum to zero. -/
private theorem sum_d4Arrow_mul_d4Arrow :
    ∑ l : zigzagD4Graph.neighborSet 1, d4Arrow k l 1 * d4Arrow k 1 l = 0 := by
  have hrel := signlessPreprojectiveMk_signlessPreprojectiveRelator k (vertex zigzagD4Graph 1)
  rw [signlessPreprojectiveRelator_congr k _ _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [d4Arrow_of_adj k l.2, d4Arrow_of_adj k (zigzagD4Graph.adj_symm l.2), ← map_mul]
  exact congrArg (signlessPreprojectiveMk k _) (ofArrow_symm_mul_ofArrow _ k l.2)

/-- The trivalent vertex of `D₄` has at most three neighbours. -/
private theorem card_neighborSet_one_le_three :
    Fintype.card (zigzagD4Graph.neighborSet 1) ≤ 3 := by
  have h := Fintype.card_subtype_lt (p := fun j => j ∈ zigzagD4Graph.neighborSet 1) (x := 1)
    (by simp)
  rw [Fintype.card_fin] at h
  exact Nat.le_of_lt_succ (by convert h)

/-- A neighbour of a leaf of `D₄` is the trivalent vertex. -/
private theorem eq_one_of_adj {i j : Fin 4} (h : zigzagD4Graph.Adj i j) (hi : i ≠ 1) : j = 1 := by
  have := (zigzagD4Graph_adj_iff i j).1 h
  tauto

/-- Every product of five composable doubled arrows of `D₄` vanishes in the signless algebra. -/
private theorem d4Arrow_mul_eq_zero {v₀ v₁ v₂ v₃ v₄ v₅ : Fin 4} (h₁ : zigzagD4Graph.Adj v₀ v₁)
    (h₂ : zigzagD4Graph.Adj v₁ v₂) (h₃ : zigzagD4Graph.Adj v₂ v₃) (h₄ : zigzagD4Graph.Adj v₃ v₄)
    (h₅ : zigzagD4Graph.Adj v₄ v₅) :
    d4Arrow k v₄ v₅ * (d4Arrow k v₃ v₄ * (d4Arrow k v₂ v₃ * (d4Arrow k v₁ v₂ *
      d4Arrow k v₀ v₁))) = 0 := by
  have hdu (l : zigzagD4Graph.neighborSet 1) : d4Arrow k 1 l * d4Arrow k l 1 = 0 :=
    d4Arrow_mul_d4Arrow_leaf k l.2
  by_cases h₀ : v₀ = 1
  · -- The path starts at the trivalent vertex, so it visits it at every even step.
    subst h₀
    obtain rfl := eq_one_of_adj h₂ h₁.ne'
    obtain rfl := eq_one_of_adj h₄ h₃.ne'
    simpa only [mul_assoc] using mul_mul_eq_zero_of_card_le_three' card_neighborSet_one_le_three
      (fun l => d4Arrow k l 1) (fun l => d4Arrow k 1 l) hdu (sum_d4Arrow_mul_d4Arrow k)
      ⟨v₁, h₁⟩ ⟨v₃, h₃⟩ ⟨v₅, h₅⟩
  · -- The path starts at a leaf, so it visits the trivalent vertex at every odd step.
    obtain rfl := eq_one_of_adj h₁ h₀
    obtain rfl := eq_one_of_adj h₃ h₂.ne'
    obtain rfl := eq_one_of_adj h₅ h₄.ne'
    simpa only [mul_assoc] using mul_mul_eq_zero_of_card_le_three card_neighborSet_one_le_three
      (fun l => d4Arrow k l 1) (fun l => d4Arrow k 1 l) hdu (sum_d4Arrow_mul_d4Arrow k)
      ⟨v₄, h₄⟩ ⟨v₂, h₂⟩ ⟨v₀, h₁.symm⟩

/-! ### Paths of length five -/

/-- **Every path of length at least five vanishes in the signless algebra of `D₄`.** -/
theorem signlessPreprojectiveMk_D4_ofPath_eq_zero_of_five_le
    (x : Quiver.TotalPath (DoubledQuiver zigzagD4Graph)) (hx : 5 ≤ x.2.2.length) :
    signlessPreprojectiveMk k _ (ofPath x) = 0 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only at hx
  induction p with
  | nil => simp at hx
  | cons q e₅ ih =>
    rw [← ofArrow_mul_ofPath, map_mul]
    by_cases hq : 5 ≤ q.length
    · rw [ih hq, mul_zero]
    have hq4 : q.length = 4 := by
      rw [Path.length_cons] at hx
      omega
    -- Peel off the remaining four arrows.
    cases q with
    | nil => simp at hq4
    | cons q e₄ =>
    cases q with
    | nil => simp at hq4
    | cons q e₃ =>
    cases q with
    | nil => simp at hq4
    | cons q e₂ =>
    cases q with
    | nil => simp at hq4
    | cons q e₁ =>
    cases q with
    | cons q e₀ => simp at hq4
    | nil =>
    rw [← ofArrow_mul_ofPath, ← ofArrow_mul_ofPath, ← ofArrow_mul_ofPath,
      ← Path.comp_toPath_eq_cons, Path.nil_comp, ← ofArrow_eq_ofPath]
    simp only [map_mul, signlessPreprojectiveMk_ofArrow]
    exact d4Arrow_mul_eq_zero k e₁.down e₂.down e₃.down e₄.down e₅.down

/-! ### Every orientation of `D₄` -/

section Orientation

variable (o : Orientation zigzagD4Graph)

/-- **Every path of length at least five vanishes in the preprojective algebra of `D₄`**, for
every orientation of the `D₄` graph. -/
theorem preprojectiveMk_D4_ofPath_eq_zero_of_five_le
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver zigzagD4Graph o)))
    (hx : 5 ≤ x.2.2.length) :
    preprojectiveMk k (OrientedQuiver zigzagD4Graph o) (ofPath x) = 0 := by
  -- Every orientation of the bipartite `D₄` graph is compared with the signless algebra.
  have hc : ∀ ⦃i j : OrientedQuiver zigzagD4Graph o⦄, (i ⟶ j) →
      zigzagD4Coloring ((OrientedQuiver.vertexEquiv _ o).symm i) ≠
        zigzagD4Coloring ((OrientedQuiver.vertexEquiv _ o).symm j) :=
    fun _ _ a => zigzagD4Coloring.valid a.1
  apply preprojectiveMk_ofPath_eq_zero_of_signless o k hc x
  exact signlessPreprojectiveMk_D4_ofPath_eq_zero_of_five_le k _
    (by rwa [Prefunctor.length_mapTotalPath])

/-- **The preprojective relation ideal of every orientation of `D₄` is admissible.** It lies in
the square of the arrow ideal, and it contains every path of length at least five. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_D4 :
    IsAdmissibleIdeal (preprojectiveIdeal k (OrientedQuiver zigzagD4Graph o)).asIdeal :=
  isAdmissibleIdeal_iff.2 ⟨⟨5, fun x hx => by
    rw [TwoSidedIdeal.mem_asIdeal, ← preprojectiveMk_eq_zero_iff]
    exact preprojectiveMk_D4_ofPath_eq_zero_of_five_le k o x hx⟩,
    preprojectiveIdeal_le_arrowIdeal_sq k⟩

end Orientation

end CommRing

/-! ### Finite dimensionality -/

section Field

variable (k : Type*) [Field k]

/-- **The preprojective algebra of `D₄` is finite-dimensional**, for every orientation of the
`D₄` graph and over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraD4 (o : Orientation zigzagD4Graph) :
    FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph o)) :=
  (isAdmissibleIdeal_preprojectiveIdeal_D4 k o).finiteDimensional_quotient

/-- **The signless algebra of `D₄` is finite-dimensional** over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraD4 :
    FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph)) :=
  (zigzagD4SignlessEquivPreprojective k).symm.toLinearEquiv.finiteDimensional

end Field

end TauCeti
