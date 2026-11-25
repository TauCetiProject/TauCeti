/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Encodable.Basic
public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.Data.List.Lex
public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.Presentation
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.NumberTheory.Padics.DenominatorColouring
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Unravelling a graph into a coloured order on `List ℚ`

A code `c : RelationalConfiguration Language.graph ℕ` is a binary relation on `ℕ`, not necessarily
symmetric or irreflexive. Colour each rational `r` by the multiplicity `ν r` of `2` in its
denominator, and read a list `x : List ℚ` as the tuple of vertices `x.map ν`. The colour
`unravelColour c x` of the node `x` encodes, injectively in `ℕ`, the length of `x` and the atomic
diagram of its tuple of vertices for `c`: for all ordered pairs `(i, j)` of indices, the diagonal
included, whether the `i`-th and `j`-th vertices are equal and the bit `c.eval (adjAtom a_i a_j)`.

The unravelling lemma says that `c` and `d` are isomorphic exactly when some order automorphism
of the lexicographic order on `List ℚ` carries the colouring of `d` back to that of `c`, and
exactly when some bijection of `List ℚ` preserving the parent `x ↦ x.dropLast` does. The forward
direction applies an order automorphism of `ℚ` realizing the relabelling of vertices entrywise;
the order and the lengths determine the parent (`List.eq_dropLast_iff`); and a parent-preserving
colour-preserving bijection gives a tuple back-and-forth system between the decoded structures.
No step uses symmetry or irreflexivity.

## Main definitions

* `TauCeti.RelationalConfiguration.ratColour`: the multiplicity of `2` in the denominator of a
  rational;
* `TauCeti.RelationalConfiguration.unravelVertex`: the vertex `ν (x.getD i 0)` at index `i` of a
  node `x`;
* `TauCeti.RelationalConfiguration.unravelColour`: the colour of a node for a code.

## Main results

* `TauCeti.RelationalConfiguration.unravelColour_eq_iff`: two colours agree exactly when the nodes
  have the same length and the same atomic diagram;
* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_orderIso_unravelColour`: the unravelling
  lemma, (i) ⇔ (ii);
* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_perm_dropLast_unravelColour`: the
  unravelling lemma, (i) ⇔ (iii).

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
-/

public section

open _root_.FirstOrder _root_.FirstOrder.Language

namespace TauCeti.RelationalConfiguration

/-- The colour `ν r` of a rational: the multiplicity of `2` in its reduced denominator. -/
noncomputable def ratColour (r : ℚ) : ℕ := multiplicity 2 r.den

theorem ratColour_def (r : ℚ) : ratColour r = multiplicity 2 r.den := (rfl)

/-- Every natural number is the colour of some rational. -/
theorem exists_ratColour_eq (m : ℕ) : ∃ r, ratColour r = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, -, -, hr⟩ := Rat.exists_multiplicity_den_eq_btwn (p := 2) m zero_lt_one
  exact ⟨r, hr⟩

/-- Every permutation of the colours is induced by an order automorphism of `ℚ`. -/
theorem exists_orderIso_ratColour (σ : Equiv.Perm ℕ) :
    ∃ π : ℚ ≃o ℚ, ∀ r, ratColour (π r) = σ (ratColour r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Rat.exists_orderIso_multiplicity_den_eq σ

/-- The vertex at index `i` of the node `x`: the colour of its `i`-th entry. -/
noncomputable def unravelVertex (x : List ℚ) (i : ℕ) : ℕ := ratColour (x.getD i 0)

theorem unravelVertex_def (x : List ℚ) (i : ℕ) : unravelVertex x i = ratColour (x.getD i 0) :=
  (rfl)

/-- The two bits recorded by the colour of `x` at the ordered pair of indices `(i, j)`: whether
the vertices are equal and whether the code relates them. -/
noncomputable def unravelBits (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ)
    (i j : ℕ) : Bool × Bool :=
  (decide (unravelVertex x i = unravelVertex x j),
    c.eval (adjAtom (unravelVertex x i) (unravelVertex x j)))

/-- The first bit at `(i, j)` records whether the two vertices are equal. -/
@[simp]
theorem unravelBits_fst (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ) (i j : ℕ) :
    (unravelBits c x i j).1 = decide (unravelVertex x i = unravelVertex x j) := (rfl)

/-- The second bit at `(i, j)` is the value of the code at the adjacency atom of the vertices. -/
@[simp]
theorem unravelBits_snd (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ) (i j : ℕ) :
    (unravelBits c x i j).2 = c.eval (adjAtom (unravelVertex x i) (unravelVertex x j)) := (rfl)

/-- The length and atomic diagram of a node, as the list of rows of its bits. -/
noncomputable def unravelDiagram (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ) :
    List (List (Bool × Bool)) :=
  (List.range x.length).map fun i ↦ (List.range x.length).map fun j ↦ unravelBits c x i j

/-- The colour `χ_c x` of the node `x` for the code `c`: an injective encoding in `ℕ` of its
length and its atomic diagram. -/
noncomputable def unravelColour (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ) : ℕ :=
  Encodable.encode (unravelDiagram c x)

/-- Two colours agree exactly when the nodes have the same length and the same bits at every
ordered pair of indices. -/
theorem unravelColour_eq_iff {c d : RelationalConfiguration Language.graph ℕ} {x y : List ℚ} :
    unravelColour c x = unravelColour d y ↔
      x.length = y.length ∧
        ∀ i < x.length, ∀ j < x.length, unravelBits c x i j = unravelBits d y i j := by
  rw [unravelColour, unravelColour, Encodable.encode_inj, unravelDiagram, unravelDiagram]
  constructor
  · intro h
    have hn : x.length = y.length := by simpa using congrArg List.length h
    refine ⟨hn, fun i hi j hj ↦ ?_⟩
    rw [hn] at h hi hj
    have h₁ := List.map_inj_left.1 h i (List.mem_range.2 hi)
    exact List.map_inj_left.1 h₁ j (List.mem_range.2 hj)
  · rintro ⟨hn, h⟩
    rw [← hn]
    refine List.map_inj_left.2 fun i hi ↦ List.map_inj_left.2 fun j hj ↦ ?_
    exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

/-- Nodes of the same colour have the same length. -/
theorem length_eq_of_unravelColour_eq {c d : RelationalConfiguration Language.graph ℕ}
    {x y : List ℚ} (h : unravelColour c x = unravelColour d y) : x.length = y.length :=
  (unravelColour_eq_iff.1 h).1

/-- The vertices of a node extended by one entry. -/
theorem unravelVertex_append_singleton {n : ℕ} {x : List ℚ} (hx : x.length = n) (r : ℚ) :
    (fun i : Fin (n + 1) ↦ unravelVertex (x ++ [r]) i) =
      Fin.snoc (fun i : Fin n ↦ unravelVertex x i) (ratColour r) := by
  subst hx
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [unravelVertex]
  · simp [unravelVertex]

/-- The relabelling `σ • c` read on the entrywise image of a node under an order automorphism
realizing `σ` on colours has the colour of the node for `c`. -/
private theorem unravelColour_map {c : RelationalConfiguration Language.graph ℕ}
    {σ : Equiv.Perm ℕ} {π : ℚ ≃o ℚ} (hπ : ∀ r, ratColour (π r) = σ (ratColour r))
    (x : List ℚ) : unravelColour (σ • c) (x.map π) = unravelColour c x := by
  refine unravelColour_eq_iff.2 ⟨List.length_map _, fun i hi j hj ↦ ?_⟩
  have hv : ∀ k < x.length, unravelVertex (x.map π) k = σ (unravelVertex x k) := fun k hk ↦ by
    rw [unravelVertex, unravelVertex, List.getD_eq_getElem _ _ (by simpa using hk),
      List.getD_eq_getElem _ _ hk, List.getElem_map, hπ]
  simp only [List.length_map] at hi hj
  simp only [unravelBits, hv i hi, hv j hj, σ.injective.eq_iff, eval_perm_smul, adjAtom_map,
    Equiv.symm_apply_apply]

/-- The entrywise image of lists under an order automorphism of `ℚ`, as an order automorphism of
the lexicographic order on `List ℚ`. -/
private def listMapOrderIso (π : ℚ ≃o ℚ) : List ℚ ≃o List ℚ where
  toFun := List.map π
  invFun := List.map π.symm
  left_inv x := by simp [List.map_map, Function.comp_def]
  right_inv x := by simp [List.map_map, Function.comp_def]
  map_rel_iff' := by
    have hmono : StrictMono (List.map π) := fun x y h ↦ by
      change List.Lex (· < ·) x y at h
      induction h with
      | nil => exact List.Lex.nil
      | cons _ ih => exact List.Lex.cons ih
      | rel h => exact List.Lex.rel (π.strictMono h)
    exact fun {_ _} ↦ hmono.le_iff_le

/-- An order automorphism of `List ℚ` preserving lengths preserves the parent. -/
private theorem dropLast_map_orderIso (Φ : List ℚ ≃o List ℚ) (hΦ : ∀ x, (Φ x).length = x.length)
    (x : List ℚ) : Φ x.dropLast = (Φ x).dropLast := by
  rcases eq_or_ne x [] with rfl | hx
  · have h0 : Φ [] = [] := by simpa using Φ.map_bot
    simp [h0]
  have hΦx : Φ x ≠ [] := by
    rw [← List.length_pos_iff, hΦ]
    exact List.length_pos_iff.2 hx
  obtain ⟨hlen, hlt, hz⟩ := (List.eq_dropLast_iff hx).1 rfl
  refine (List.eq_dropLast_iff hΦx).2 ⟨by rw [hΦ, hΦ, hlen], Φ.lt_iff_lt.2 hlt, fun z h₁ h₂ ↦ ?_⟩
  rw [← Φ.apply_symm_apply z] at h₁ h₂ ⊢
  rw [Φ.lt_iff_lt] at h₁ h₂
  rw [hΦ, hΦ]
  exact hz _ h₁ h₂

/-- A list whose parent is `x` and which is one longer than `x` is a child `x ++ [r]` of `x`. -/
private theorem exists_eq_append_singleton {x y : List ℚ} (hy : y.dropLast = x)
    (hl : y.length = x.length + 1) : ∃ r, y = x ++ [r] :=
  ⟨y.getLast (by rintro rfl; simp at hl), by
    conv_lhs => rw [← List.dropLast_append_getLast (l := y) (by rintro rfl; simp at hl)]
    rw [hy]⟩

/-- The pairs of vertex tuples of a node `x` and of its image `Ψ x`. -/
private def unravelSystem (Ψ : Equiv.Perm (List ℚ)) : Set (Σ n, (Fin n → ℕ) × (Fin n → ℕ)) :=
  {p | ∃ x : List ℚ, x.length = p.1 ∧ p.2.1 = (fun i : Fin p.1 ↦ unravelVertex x i) ∧
    p.2.2 = fun i : Fin p.1 ↦ unravelVertex (Ψ x) i}

/-- The vertex tuples of a node and of its image have the same atomic type when the colours
agree. -/
private theorem sameAtomicType_unravelVertex {c d : RelationalConfiguration Language.graph ℕ}
    {x y : List ℚ} {n : ℕ} (hx : x.length = n) (h : unravelColour c x = unravelColour d y) :
    @SameAtomicType Language.graph n ℕ ℕ c.toStructure d.toStructure _
      (fun i : Fin n ↦ unravelVertex x i) (fun i : Fin n ↦ unravelVertex y i) := by
  obtain ⟨-, hbits⟩ := unravelColour_eq_iff.1 h
  have hb (i j : Fin n) := hbits i (hx ▸ i.isLt) j (hx ▸ j.isLt)
  refine (@sameAtomicType_iff Language.graph n ℕ ℕ c.toStructure d.toStructure _ _ _).2
    ⟨fun i j ↦ by simpa using congrArg Prod.fst (hb i j), fun {k} r f ↦ ?_⟩
  rw [toStructure_relMap, toStructure_relMap]
  cases r
  have hf (v : Fin n → ℕ) : v ∘ f = ![v (f 0), v (f 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hf, hf, ← adjAtom_def, ← adjAtom_def]
  have := congrArg Prod.snd (hb (f 0) (f 1))
  simp only [unravelBits_snd] at this
  rw [this]

/-- A bijection of `List ℚ` preserving the parent and the colours gives an isomorphism of the
codes, through a tuple back-and-forth system of vertex tuples of matching nodes. -/
private theorem isoSetoid_of_perm_dropLast {c d : RelationalConfiguration Language.graph ℕ}
    (Ψ : Equiv.Perm (List ℚ)) (hΨ : ∀ x, Ψ x.dropLast = (Ψ x).dropLast)
    (hχ : unravelColour d ∘ Ψ = unravelColour c) : isoSetoid Language.graph ℕ c d := by
  have hχ' (x : List ℚ) : unravelColour d (Ψ x) = unravelColour c x := congrFun hχ x
  have hlen (x : List ℚ) : (Ψ x).length = x.length := length_eq_of_unravelColour_eq (hχ' x)
  -- a node and its image have children of every colour, matched by `Ψ`
  have hchild (x : List ℚ) (r : ℚ) : ∃ s, Ψ (x ++ [r]) = Ψ x ++ [s] :=
    exists_eq_append_singleton (by simp [← hΨ]) (by simp [hlen])
  have hchild' (x : List ℚ) (s : ℚ) : ∃ r, Ψ (x ++ [r]) = Ψ x ++ [s] := by
    obtain ⟨r, hr⟩ := exists_eq_append_singleton (x := x) (y := Ψ.symm (Ψ x ++ [s]))
      (Ψ.injective (by simp [hΨ])) (by rw [← hlen]; simp [hlen])
    exact ⟨r, by rw [← hr, Equiv.apply_symm_apply]⟩
  have hS : @IsTupleBFSystem Language.graph _ ℕ ℕ c.toStructure d.toStructure
      (unravelSystem Ψ) := by
    refine @IsTupleBFSystem.mk Language.graph _ ℕ ℕ c.toStructure d.toStructure _
      ⟨[], rfl, funext (·.elim0), funext (·.elim0)⟩ ?_ ?_ ?_ <;>
      rintro n a b ⟨x, hx, ha, hb⟩ <;> dsimp only at hx ha hb <;> subst ha hb
    · exact sameAtomicType_unravelVertex hx (hχ' x).symm
    · intro m
      obtain ⟨r, rfl⟩ := exists_ratColour_eq m
      obtain ⟨s, hs⟩ := hchild x r
      exact ⟨ratColour s, x ++ [r], by simp [hx], (unravelVertex_append_singleton hx r).symm,
        by rw [hs, unravelVertex_append_singleton (by rw [hlen, hx])]⟩
    · intro m
      obtain ⟨s, rfl⟩ := exists_ratColour_eq m
      obtain ⟨r, hr⟩ := hchild' x s
      exact ⟨ratColour r, x ++ [r], by simp [hx], (unravelVertex_append_singleton hx r).symm,
        by rw [hr, unravelVertex_append_singleton (by rw [hlen, hx])]⟩
  have hP := (@potentialIso_iff_exists_isTupleBFSystem Language.graph _ ℕ ℕ c.toStructure
    d.toStructure).2 ⟨_, hS⟩
  exact isoSetoid_apply.2 <|
    (@countable_potentialIso_iff_iso Language.graph ℕ ℕ c.toStructure d.toStructure _ _).1 hP

/-- **Unravelling lemma, (i) ⇒ (ii) ⇒ (iii) ⇒ (i).** For codes `c` and `d` of the language of
graphs, not necessarily simple graphs, `c` and `d` are isomorphic exactly when some order
automorphism `Φ` of `List ℚ` satisfies `χ_d ∘ Φ = χ_c`. -/
theorem isoSetoid_iff_exists_orderIso_unravelColour
    {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.graph ℕ c d ↔
      ∃ Φ : List ℚ ≃o List ℚ, unravelColour d ∘ Φ = unravelColour c := by
  refine ⟨fun h ↦ ?_, fun ⟨Φ, hΦ⟩ ↦ ?_⟩
  · obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
    obtain ⟨π, hπ⟩ := exists_orderIso_ratColour σ
    exact ⟨listMapOrderIso π, funext fun x ↦ unravelColour_map hπ x⟩
  · have hlen (x : List ℚ) : (Φ x).length = x.length :=
      length_eq_of_unravelColour_eq (congrFun hΦ x)
    exact isoSetoid_of_perm_dropLast Φ.toEquiv (dropLast_map_orderIso Φ hlen) hΦ

/-- **Unravelling lemma, (i) ⇔ (iii).** For codes `c` and `d` of the language of graphs, not
necessarily simple graphs, `c` and `d` are isomorphic exactly when some bijection `Ψ` of
`List ℚ` preserving the parent `x ↦ x.dropLast` satisfies `χ_d ∘ Ψ = χ_c`. -/
theorem isoSetoid_iff_exists_perm_dropLast_unravelColour
    {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.graph ℕ c d ↔
      ∃ Ψ : Equiv.Perm (List ℚ), (∀ x, Ψ x.dropLast = (Ψ x).dropLast) ∧
        unravelColour d ∘ Ψ = unravelColour c := by
  refine ⟨fun h ↦ ?_, fun ⟨Ψ, hΨ, hχ⟩ ↦ isoSetoid_of_perm_dropLast Ψ hΨ hχ⟩
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColour.1 h
  have hlen (x : List ℚ) : (Φ x).length = x.length :=
    length_eq_of_unravelColour_eq (congrFun hΦ x)
  exact ⟨Φ.toEquiv, dropLast_map_orderIso Φ hlen, hΦ⟩

end TauCeti.RelationalConfiguration
