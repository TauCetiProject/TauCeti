/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.FlagTwoSkeletonQuotient
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The coned-off Cayley graph of a group relative to a family of subgroups

Let `G` be a group, `A` a set of elements of `G` and `ℋ` a family of subgroups of `G`. The
*relative Cayley graph* `TauCeti.Group.relCayleyGraph A ℋ` has as vertices the elements of `G`
and the left cosets `g H` of the subgroups `H ∈ ℋ`. An element `g` is joined to `g a` for every
`a ∈ A` with `g a ≠ g`, and to its coset `g H` for every `H ∈ ℋ`; two cosets are never joined.
On the elements of `G` it is the Cayley graph `SimpleGraph.mulCayley A`, and the coset `g H` is a
cone vertex over the elements of `g H`. The group `G` acts on it by left multiplication, freely on
the elements of `G`, and the stabilizer of the coset `g H` is `g H g⁻¹`.

Guirardel and Levitt attach to a presentation of `G` relative to `ℋ` a two-complex whose universal
cover contains, for every `H ∈ ℋ`, lifts of a subcomplex carrying `H`. When `A` consists of the
images of the generators and of the subwords of the relators, the flag complex of this graph
contains the relator discs triangulated by fans and plays the role of that universal cover, with
every such lift coned off to a point. For finite `A` and `ℋ` the action has finitely many orbits of
vertices, edges and triangles: this is the cocompactness used by Dunwoody's bound on the number
of non-parallel tracks.

## Main definitions

* `TauCeti.Group.RelCayleyVertex`: the vertices, `G ⊕ Σ H : ℋ, G ⧸ H`, with the action of `G`
  by left multiplication.
* `TauCeti.Group.relCayleyGraph`: the relative Cayley graph.

## Main results

* `TauCeti.Group.comap_inl_relCayleyGraph`: on the elements of `G` it is the Cayley graph.
* `TauCeti.Group.relCayleyGraph_adj_smul_iff`: left multiplication preserves adjacency.
* `TauCeti.Group.stabilizer_relCayleyVertex_inl`, `TauCeti.Group.stabilizer_relCayleyVertex_inr`:
  the action is free on the elements of `G`, and the stabilizer of `g H` is `g H g⁻¹`.
* `TauCeti.Group.hasFiniteFlagTwoSkeletonQuotient_relCayleyGraph`: for finite `A` and `ℋ`
  there are finitely many orbits of vertices, edges and triangles.
* `TauCeti.Group.relCayleyGraph_connected_iff`: the graph is connected exactly when `A` and the
  subgroups in `ℋ` generate `G`.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §2.5: the
  two-complex of a relative finite presentation, before the proof of Proposition 2.24.
* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups) and §2, Theorem 2.2 (the bound on non-parallel
  tracks).
-/

public section

namespace TauCeti

open _root_.MulAction

namespace Group

variable {G : Type*} [Group G]

/-- The vertices of the relative Cayley graph: the elements of `G` and the left cosets of the
subgroups in the family `ℋ`. The group `G` acts on them by left multiplication. -/
abbrev RelCayleyVertex (ℋ : Set (Subgroup G)) :=
  G ⊕ (Σ H : ℋ, G ⧸ (H : Subgroup G))

/-- The relative Cayley graph of `G` with respect to a set `A` of elements and a family `ℋ` of
subgroups: `g` is adjacent to `g a` for `a ∈ A` (when they are distinct), and to its coset
`g H` for every `H ∈ ℋ`. -/
def relCayleyGraph (A : Set G) (ℋ : Set (Subgroup G)) : SimpleGraph (RelCayleyVertex ℋ) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl g, .inl g' => g⁻¹ * g' ∈ A
    | .inl g, .inr ⟨_, c⟩ => (g : G ⧸ _) = c
    | _, _ => False

variable {A : Set G} {ℋ : Set (Subgroup G)}

/-- Two elements of `G` are adjacent exactly when they are distinct and differ on the right by an
element of `A` or of its inverse. -/
@[simp] theorem relCayleyGraph_adj_inl_inl {g g' : G} :
    (relCayleyGraph A ℋ).Adj (.inl g) (.inl g') ↔ g ≠ g' ∧ (g⁻¹ * g' ∈ A ∨ g'⁻¹ * g ∈ A) := by
  simp [relCayleyGraph]

/-- An element `g` of `G` is adjacent to a coset of a subgroup in the family exactly when the
coset is `g H`. -/
@[simp] theorem relCayleyGraph_adj_inl_inr {g : G} {H : ℋ} {c : G ⧸ (H : Subgroup G)} :
    (relCayleyGraph A ℋ).Adj (.inl g) (.inr ⟨H, c⟩) ↔ (g : G ⧸ (H : Subgroup G)) = c := by
  simp [relCayleyGraph]

/-- A coset of a subgroup in the family is adjacent to an element `g` of `G` exactly when the
coset is `g H`. -/
@[simp] theorem relCayleyGraph_adj_inr_inl {g : G} {H : ℋ} {c : G ⧸ (H : Subgroup G)} :
    (relCayleyGraph A ℋ).Adj (.inr ⟨H, c⟩) (.inl g) ↔ (g : G ⧸ (H : Subgroup G)) = c := by
  rw [SimpleGraph.adj_comm, relCayleyGraph_adj_inl_inr]

/-- Two cosets are never adjacent. -/
@[simp] theorem not_relCayleyGraph_adj_inr_inr {x y : Σ H : ℋ, G ⧸ (H : Subgroup G)} :
    ¬(relCayleyGraph A ℋ).Adj (.inr x) (.inr y) := by
  simp [relCayleyGraph]

/-- On the elements of `G`, the relative Cayley graph is the Cayley graph of `A`. -/
@[simp] theorem comap_inl_relCayleyGraph :
    (relCayleyGraph A ℋ).comap Sum.inl = SimpleGraph.mulCayley A := by
  ext
  simp [SimpleGraph.mulCayley_adj]

/-- Left multiplication preserves the relative Cayley graph. -/
@[simp] theorem relCayleyGraph_adj_smul_iff (g : G) {x y : RelCayleyVertex ℋ} :
    (relCayleyGraph A ℋ).Adj (g • x) (g • y) ↔ (relCayleyGraph A ℋ).Adj x y := by
  rcases x with x | ⟨H, c⟩ <;> rcases y with y | ⟨H', c'⟩
  · simp [mul_assoc]
  · induction c' using QuotientGroup.induction_on
    simp
  · induction c using QuotientGroup.induction_on
    simp
  · simp

/-- The group acts freely on the vertices of the relative Cayley graph which are group
elements. -/
theorem stabilizer_relCayleyVertex_inl (g : G) :
    stabilizer G (Sum.inl g : RelCayleyVertex ℋ) = ⊥ := by
  ext
  simp

/-- The stabilizer of the coset vertex `H` is the subgroup `H` itself. -/
theorem stabilizer_relCayleyVertex_inr_one (H : ℋ) :
    stabilizer G (Sum.inr ⟨H, ((1 : G) : G ⧸ (H : Subgroup G))⟩ : RelCayleyVertex ℋ) = H := by
  ext
  simp [QuotientGroup.eq]

/-- The stabilizer of the coset vertex `g H` is the conjugate `g H g⁻¹`. -/
theorem stabilizer_relCayleyVertex_inr (H : ℋ) (g : G) :
    stabilizer G (Sum.inr ⟨H, (g : G ⧸ (H : Subgroup G))⟩ : RelCayleyVertex ℋ) =
      (H : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  have : (Sum.inr ⟨H, (g : G ⧸ (H : Subgroup G))⟩ : RelCayleyVertex ℋ) =
      g • Sum.inr ⟨H, ((1 : G) : G ⧸ (H : Subgroup G))⟩ := by simp
  rw [this, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_relCayleyVertex_inr_one]

/-- The vertices of a clique on at most three vertices are all equal or adjacent to one group
element. -/
private theorem exists_forall_eq_or_adj_of_isClique {a b c : RelCayleyVertex ℋ}
    (h : (relCayleyGraph A ℋ).IsClique {a, b, c}) :
    ∃ g : G, ∀ x ∈ ({a, b, c} : Set (RelCayleyVertex ℋ)),
      x = .inl g ∨ (relCayleyGraph A ℋ).Adj (.inl g) x := by
  by_cases hs : ∃ g, Sum.inl g ∈ ({a, b, c} : Set (RelCayleyVertex ℋ))
  · obtain ⟨g, hg⟩ := hs
    exact ⟨g, fun x hx => (eq_or_ne x (.inl g)).imp_right fun hne => h hg hx hne.symm⟩
  simp only [not_exists] at hs
  -- otherwise the three vertices are cosets, which are pairwise non-adjacent, hence equal
  have key : ∀ x ∈ ({a, b, c} : Set (RelCayleyVertex ℋ)), x = a := by
    intro x hx
    by_contra hne
    rcases x with g | x
    · exact hs g hx
    rcases a with g | a
    · exact hs g (by simp)
    exact not_relCayleyGraph_adj_inr_inr (h hx (by simp) hne)
  rcases a with g | ⟨H, c⟩
  · exact (hs g (by simp)).elim
  induction c using QuotientGroup.induction_on with | H g =>
  exact ⟨g, fun x hx => .inr (key x hx ▸ relCayleyGraph_adj_inl_inr.2 rfl)⟩

/-- For finite `A` and a finite family `ℋ`, left multiplication has finitely many orbits of
vertices, edges and triangles of the relative Cayley graph. -/
theorem hasFiniteFlagTwoSkeletonQuotient_relCayleyGraph (hA : A.Finite) (hℋ : ℋ.Finite) :
    (relCayleyGraph A ℋ).HasFiniteFlagTwoSkeletonQuotient G := by
  have hfin : ((relCayleyGraph A ℋ).neighborSet (.inl 1)).Finite := by
    have := hℋ.to_subtype
    refine (((hA.union (hA.preimage inv_injective.injOn)).image Sum.inl).union
      (Set.finite_range fun H : ℋ =>
        (Sum.inr ⟨H, ((1 : G) : G ⧸ (H : Subgroup G))⟩ : RelCayleyVertex ℋ))).subset ?_
    rintro (g | ⟨H, c⟩) hx <;> simp_all
  refine SimpleGraph.hasFiniteFlagTwoSkeletonQuotient_iff.2
    ⟨insert (.inl 1) ((relCayleyGraph A ℋ).neighborSet (.inl 1)), hfin.insert _,
      fun a b c habc => ?_⟩
  obtain ⟨g, hg⟩ := exists_forall_eq_or_adj_of_isClique habc
  have key (x) (hx : x ∈ ({a, b, c} : Set (RelCayleyVertex ℋ))) :
      g⁻¹ • x ∈ insert (.inl 1) ((relCayleyGraph A ℋ).neighborSet (.inl 1)) := by
    rcases hg x hx with rfl | hx
    · simp
    · exact Set.mem_insert_of_mem _ (by simpa using (relCayleyGraph_adj_smul_iff g⁻¹).2 hx)
  exact ⟨g⁻¹, key a (by simp), key b (by simp), key c (by simp)⟩

/-- Every vertex of the relative Cayley graph is reachable from the identity when `A` and the
subgroups in the family generate `G`. -/
private theorem reachable_inl_one_of_sup_eq_top (h : Subgroup.closure A ⊔ sSup ℋ = ⊤)
    (v : RelCayleyVertex ℋ) : (relCayleyGraph A ℋ).Reachable (.inl 1) v := by
  -- the elements `k` such that every `g` is joined to `g * k` form a subgroup
  let K : Subgroup G :=
    { carrier := {k | ∀ g, (relCayleyGraph A ℋ).Reachable (.inl g) (.inl (g * k))}
      one_mem' := fun g => by simp
      mul_mem' := fun {a _} ha hb g => (ha g).trans (by simpa [mul_assoc] using hb (g * a))
      inv_mem' := fun {a} ha g => by simpa using (ha (g * a⁻¹)).symm }
  have hA : Subgroup.closure A ≤ K := (Subgroup.closure_le K).2 fun a ha g => by
    by_cases hga : g = g * a
    · rw [← hga]
    · exact (relCayleyGraph_adj_inl_inl.2 ⟨hga, .inl (by simpa using ha)⟩).reachable
  -- `g` and `g * a` are both joined to the coset `g H`
  have hℋ : sSup ℋ ≤ K := sSup_le fun H hH a ha g =>
    ((relCayleyGraph_adj_inl_inr (H := ⟨H, hH⟩) (c := (g : G ⧸ H))).2 rfl).reachable.trans
      ((relCayleyGraph_adj_inr_inl (H := ⟨H, hH⟩)).2 (by simpa [QuotientGroup.eq])).reachable
  have hK (g : G) : (relCayleyGraph A ℋ).Reachable (.inl 1) (.inl g) := by
    simpa using h.ge.trans (sup_le hA hℋ) (Subgroup.mem_top g) 1
  rcases v with g | ⟨H, c⟩
  · exact hK g
  · induction c using QuotientGroup.induction_on with | H g =>
    exact (hK g).trans (relCayleyGraph_adj_inl_inr.2 rfl).reachable

/-- An element of `G` joined to the identity in the relative Cayley graph lies in the subgroup
generated by `A` and the subgroups in the family. -/
private theorem mem_sup_of_reachable_inl_one {g : G}
    (h : (relCayleyGraph A ℋ).Reachable (.inl 1) (.inl g)) : g ∈ Subgroup.closure A ⊔ sSup ℋ := by
  set K := Subgroup.closure A ⊔ sSup ℋ
  -- the vertices `g` and `g H` with `g ∈ K` are closed under adjacency
  let P : RelCayleyVertex ℋ → Prop
    | .inl g => g ∈ K
    | .inr ⟨H, c⟩ => ∀ g : G, (g : G ⧸ (H : Subgroup G)) = c → g ∈ K
  have step {u v : RelCayleyVertex ℋ} (huv : (relCayleyGraph A ℋ).Adj u v) (hu : P u) : P v := by
    rcases u with g | ⟨H, c⟩ <;> rcases v with g' | ⟨H', c'⟩
    · rcases (relCayleyGraph_adj_inl_inl.1 huv).2 with h' | h'
      · simpa using K.mul_mem hu (Subgroup.mem_sup_left (Subgroup.subset_closure h'))
      · simpa using K.mul_mem hu (K.inv_mem (Subgroup.mem_sup_left (Subgroup.subset_closure h')))
    · rintro g'' rfl
      have : g⁻¹ * g'' ∈ K := Subgroup.mem_sup_right
        (le_sSup H'.2 (QuotientGroup.eq.1 (relCayleyGraph_adj_inl_inr.1 huv)))
      simpa using K.mul_mem hu this
    · exact hu g' (relCayleyGraph_adj_inr_inl.1 huv)
    · exact (not_relCayleyGraph_adj_inr_inr huv).elim
  obtain ⟨w⟩ := h
  have key {u v : RelCayleyVertex ℋ} (w : (relCayleyGraph A ℋ).Walk u v) : P u → P v := by
    induction w with
    | nil => exact id
    | cons huv _ ih => exact fun hu => ih (step huv hu)
  exact key w K.one_mem

/-- The relative Cayley graph is connected exactly when `A` and the subgroups in the family
generate `G`. -/
theorem relCayleyGraph_connected_iff :
    (relCayleyGraph A ℋ).Connected ↔ Subgroup.closure A ⊔ sSup ℋ = ⊤ :=
  ⟨fun h => (Subgroup.eq_top_iff' _).2 fun _ => mem_sup_of_reachable_inl_one (h.preconnected _ _),
    fun h => (SimpleGraph.connected_iff _).2 ⟨fun u v =>
      (reachable_inl_one_of_sup_eq_top h u).symm.trans (reachable_inl_one_of_sup_eq_top h v),
      ⟨.inl 1⟩⟩⟩

end Group

end TauCeti
