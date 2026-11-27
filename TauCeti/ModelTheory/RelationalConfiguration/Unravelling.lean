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
`unravelColor c x` of the node `x` encodes, injectively in `ℕ`, the length of `x` and the atomic
diagram of its tuple of vertices for `c`: for all ordered pairs `(i, j)` of indices, the diagonal
included, whether the `i`-th and `j`-th vertices are equal and the bit `c.eval (adjAtom a_i a_j)`.

The unravelling lemma says that `c` and `d` are isomorphic exactly when some order automorphism
of the lexicographic order on `List ℚ` carries the colouring of `d` back to that of `c`, and
exactly when some bijection of `List ℚ` preserving the parent `x ↦ x.dropLast` does. The forward
direction applies an order automorphism of `ℚ` realizing the relabelling of vertices entrywise;
the order and the lengths determine the parent (`OrderIso.map_dropLast`); and a parent-preserving
colour-preserving bijection gives a tuple back-and-forth system between the decoded structures.
No step uses symmetry or irreflexivity.

## Main definitions

* `TauCeti.RelationalConfiguration.ratColor`: the multiplicity of `2` in the denominator of a
  rational;
* `TauCeti.RelationalConfiguration.unravelVertex`: the vertex `ν (x.getD i 0)` at index `i` of a
  node `x`;
* `TauCeti.RelationalConfiguration.unravelColor`: the colour of a node for a code.

## Main results

* `TauCeti.RelationalConfiguration.unravelColor_eq_iff`: two colours agree exactly when the nodes
  have the same length and the same atomic diagram;
* `TauCeti.RelationalConfiguration.continuous_unravelColor`: the colour of a node depends
  continuously on the code (it reads finitely many coordinates);
* `TauCeti.RelationalConfiguration.unravelColor_eq_iff_sameAtomicType`: two nodes of the same length
  have the same colour exactly when their vertex tuples have the same atomic type;
* `TauCeti.RelationalConfiguration.unravelColor_map`: the colour for a relabelled code `σ • c` of
  a node mapped entrywise by a function realizing `σ` on colours is the colour for `c`;
* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_orderIso_unravelColor`: the unravelling
  lemma, (i) ⇔ (ii);
* `TauCeti.RelationalConfiguration.isoSetoid_iff_exists_perm_dropLast_unravelColor`: the
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
noncomputable def ratColor (r : ℚ) : ℕ := multiplicity 2 r.den

theorem ratColor_def (r : ℚ) : ratColor r = multiplicity 2 r.den := (rfl)

/-- Integers have colour `0`. -/
@[simp]
theorem ratColor_intCast (n : ℤ) : ratColor n = 0 := by
  simp [ratColor_def]

/-- Natural numbers have colour `0`. -/
@[simp]
theorem ratColor_natCast (n : ℕ) : ratColor n = 0 := by
  simp [ratColor_def]

/-- Numerals have colour `0`. -/
@[simp]
theorem ratColor_ofNat (n : ℕ) : ratColor (no_index (OfNat.ofNat n)) = 0 := by
  simp [ratColor_def]

/-- The colour of `1 / 2 ^ k` is `k`. -/
@[simp]
theorem ratColor_inv_two_pow (k : ℕ) : ratColor (2 ^ k)⁻¹ = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : ((2 : ℚ) ^ k)⁻¹.den = 2 ^ k := by
    rw [show (2 : ℚ) ^ k = ((2 ^ k : ℕ) : ℚ) by norm_cast, Rat.inv_natCast_den]
    simp
  rw [ratColor_def, h, Nat.multiplicity_prime_pow]

/-- The colour of `1 / 2` is `1`. -/
@[simp]
theorem ratColor_inv_two : ratColor 2⁻¹ = 1 := by
  simpa using ratColor_inv_two_pow 1

/-- Every natural number is the colour of some rational. -/
theorem exists_ratColor_eq (m : ℕ) : ∃ r, ratColor r = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, -, -, hr⟩ := Rat.exists_multiplicity_den_eq_btwn (p := 2) m zero_lt_one
  exact ⟨r, hr⟩

/-- Every permutation of the colours is induced by an order automorphism of `ℚ`. -/
theorem exists_orderIso_ratColor (σ : Equiv.Perm ℕ) :
    ∃ π : ℚ ≃o ℚ, ∀ r, ratColor (π r) = σ (ratColor r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Rat.exists_orderIso_multiplicity_den_eq σ

/-- The vertex at index `i` of the node `x`: the colour of its `i`-th entry. -/
noncomputable def unravelVertex (x : List ℚ) (i : ℕ) : ℕ := ratColor (x.getD i 0)

theorem unravelVertex_def (x : List ℚ) (i : ℕ) : unravelVertex x i = ratColor (x.getD i 0) :=
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
private noncomputable def unravelDiagram (c : RelationalConfiguration Language.graph ℕ)
    (x : List ℚ) : List (List (Bool × Bool)) :=
  (List.range x.length).map fun i ↦ (List.range x.length).map fun j ↦ unravelBits c x i j

/-- The colour `χ_c x` of the node `x` for the code `c`: an injective encoding in `ℕ` of its
length and its atomic diagram. -/
noncomputable def unravelColor (c : RelationalConfiguration Language.graph ℕ) (x : List ℚ) : ℕ :=
  Encodable.encode (unravelDiagram c x)

/-- Two colours agree exactly when the nodes have the same length and the same bits at every
ordered pair of indices. -/
theorem unravelColor_eq_iff {c d : RelationalConfiguration Language.graph ℕ} {x y : List ℚ} :
    unravelColor c x = unravelColor d y ↔
      x.length = y.length ∧
        ∀ i < x.length, ∀ j < x.length, unravelBits c x i j = unravelBits d y i j := by
  rw [unravelColor, unravelColor, Encodable.encode_inj, unravelDiagram, unravelDiagram]
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

open Filter Topology in
/-- **The colour of a node depends continuously on the code**: it reads the finitely many
coordinates `c.eval (adjAtom a_i a_j)` of the vertex tuple `a` of the node. -/
theorem continuous_unravelColor (x : List ℚ) :
    Continuous fun c : RelationalConfiguration Language.graph ℕ => unravelColor c x := by
  refine continuous_iff_continuousAt.2 fun c => ?_
  have hev (a : Atom Language.graph ℕ) : ∀ᶠ d in 𝓝 c, d.eval a = c.eval a :=
    (continuous_eval a).continuousAt ((isOpen_discrete {c.eval a}).mem_nhds rfl)
  have h : ∀ᶠ d in 𝓝 c, ∀ i : Fin x.length, ∀ j : Fin x.length,
      d.eval (adjAtom (unravelVertex x i) (unravelVertex x j)) =
        c.eval (adjAtom (unravelVertex x i) (unravelVertex x j)) :=
    eventually_all.2 fun i => eventually_all.2 fun j => hev _
  refine (continuousAt_const (y := unravelColor c x)).congr (h.mono fun d hd => ?_)
  refine unravelColor_eq_iff.2 ⟨rfl, fun i hi j hj => ?_⟩
  exact Prod.ext (by simp) (by simpa using (hd ⟨i, hi⟩ ⟨j, hj⟩).symm)

/-- Nodes of the same colour have the same length. -/
theorem length_eq_of_unravelColor_eq {c d : RelationalConfiguration Language.graph ℕ}
    {x y : List ℚ} (h : unravelColor c x = unravelColor d y) : x.length = y.length :=
  (unravelColor_eq_iff.1 h).1

/-- The vertices of a node extended by one entry. -/
theorem unravelVertex_append_singleton {n : ℕ} {x : List ℚ} (hx : x.length = n) (r : ℚ) :
    (fun i : Fin (n + 1) ↦ unravelVertex (x ++ [r]) i) =
      Fin.snoc (fun i : Fin n ↦ unravelVertex x i) (ratColor r) := by
  subst hx
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [unravelVertex]
  · simp [unravelVertex]

/-- Mapping a node entrywise by a function realizing `σ` on colours applies `σ` to each of its
vertices. -/
theorem unravelVertex_map {σ : ℕ → ℕ} {π : ℚ → ℚ} (hπ : ∀ r, ratColor (π r) = σ (ratColor r))
    {x : List ℚ} {k : ℕ} (hk : k < x.length) :
    unravelVertex (x.map π) k = σ (unravelVertex x k) := by
  simp [unravelVertex, List.getElem?_eq_getElem hk, hπ]

/-- The relabelling `σ • c` read on the entrywise image of a node under a function realizing `σ`
on colours has the colour of the node for `c`. -/
theorem unravelColor_map {c : RelationalConfiguration Language.graph ℕ}
    {σ : Equiv.Perm ℕ} {π : ℚ → ℚ} (hπ : ∀ r, ratColor (π r) = σ (ratColor r))
    (x : List ℚ) : unravelColor (σ • c) (x.map π) = unravelColor c x := by
  refine unravelColor_eq_iff.2 ⟨List.length_map _, fun i hi j hj ↦ ?_⟩
  simp only [List.length_map] at hi hj
  simp only [unravelBits, unravelVertex_map hπ hi, unravelVertex_map hπ hj, σ.injective.eq_iff,
    eval_perm_smul, adjAtom_map, Equiv.symm_apply_apply]

/-- The pairs of vertex tuples of a node `x` and of its image `Ψ x`. -/
private def unravelSystem (Ψ : Equiv.Perm (List ℚ)) : Set (Σ n, (Fin n → ℕ) × (Fin n → ℕ)) :=
  {p | ∃ x : List ℚ, x.length = p.1 ∧ p.2.1 = (fun i : Fin p.1 ↦ unravelVertex x i) ∧
    p.2.2 = fun i : Fin p.1 ↦ unravelVertex (Ψ x) i}

/-- Two nodes of length `n` have the same colour exactly when their vertex tuples have the same
atomic type in the decoded structures. -/
theorem unravelColor_eq_iff_sameAtomicType {c d : RelationalConfiguration Language.graph ℕ}
    {x y : List ℚ} {n : ℕ} (hx : x.length = n) (hy : y.length = n) :
    unravelColor c x = unravelColor d y ↔
      @SameAtomicType Language.graph n ℕ ℕ c.toStructure d.toStructure _
        (fun i : Fin n ↦ unravelVertex x i) (fun i : Fin n ↦ unravelVertex y i) := by
  have hf (v : Fin n → ℕ) (f : Fin 2 → Fin n) : v ∘ f = ![v (f 0), v (f 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [@sameAtomicType_iff Language.graph n ℕ ℕ c.toStructure d.toStructure _ _ _,
    unravelColor_eq_iff]
  constructor
  · rintro ⟨-, hbits⟩
    have hb (i j : Fin n) := hbits i (hx ▸ i.isLt) j (hx ▸ j.isLt)
    refine ⟨fun i j ↦ by simpa using congrArg Prod.fst (hb i j), fun {k} r f ↦ ?_⟩
    rw [toStructure_relMap, toStructure_relMap]
    cases r
    rw [hf, hf, ← adjAtom_def, ← adjAtom_def]
    have := congrArg Prod.snd (hb (f 0) (f 1))
    simp only [unravelBits_snd] at this
    rw [this]
  · rintro ⟨heq, hrel⟩
    refine ⟨hx.trans hy.symm, fun i hi j hj ↦ ?_⟩
    have hadj := hrel Language.adj ![⟨i, hx ▸ hi⟩, ⟨j, hx ▸ hj⟩]
    rw [toStructure_relMap, toStructure_relMap, hf, hf, ← adjAtom_def, ← adjAtom_def] at hadj
    exact Prod.ext (by simpa using heq ⟨i, hx ▸ hi⟩ ⟨j, hx ▸ hj⟩)
      (by simpa using Bool.eq_iff_iff.2 hadj)

/-- A bijection of `List ℚ` preserving the parent and the colours gives an isomorphism of the
codes, through a tuple back-and-forth system of vertex tuples of matching nodes. -/
private theorem isoSetoid_of_perm_dropLast {c d : RelationalConfiguration Language.graph ℕ}
    (Ψ : Equiv.Perm (List ℚ)) (hΨ : ∀ x, Ψ x.dropLast = (Ψ x).dropLast)
    (hχ : unravelColor d ∘ Ψ = unravelColor c) : isoSetoid Language.graph ℕ c d := by
  have hχ' (x : List ℚ) : unravelColor d (Ψ x) = unravelColor c x := congrFun hχ x
  have hlen (x : List ℚ) : (Ψ x).length = x.length := length_eq_of_unravelColor_eq (hχ' x)
  -- a node and its image have children of every colour, matched by `Ψ`
  have hchild (x : List ℚ) (r : ℚ) : ∃ s, Ψ (x ++ [r]) = Ψ x ++ [s] := by
    have hne : Ψ (x ++ [r]) ≠ [] := List.ne_nil_of_length_pos (by simp [hlen])
    have hd : (Ψ (x ++ [r])).dropLast = Ψ x := by simp [← hΨ]
    exact ⟨_, hd ▸ (List.dropLast_append_getLast hne).symm⟩
  have hchild' (x : List ℚ) (s : ℚ) : ∃ r, Ψ (x ++ [r]) = Ψ x ++ [s] := by
    obtain ⟨l, hl⟩ := Ψ.surjective (Ψ x ++ [s])
    have hne : l ≠ [] := List.ne_nil_of_length_pos (by simp [← hlen l, hl])
    have hd : l.dropLast = x := Ψ.injective (by simp [hΨ, hl])
    refine ⟨l.getLast hne, ?_⟩
    rw [← hl, ← hd, List.dropLast_append_getLast]
  have hS : @IsTupleBFSystem Language.graph _ ℕ ℕ c.toStructure d.toStructure
      (unravelSystem Ψ) := by
    refine @IsTupleBFSystem.mk Language.graph _ ℕ ℕ c.toStructure d.toStructure _
      ⟨[], rfl, funext (·.elim0), funext (·.elim0)⟩ ?_ ?_ ?_ <;>
      rintro n a b ⟨x, hx, ha, hb⟩ <;> dsimp only at hx ha hb <;> subst ha hb
    · exact (unravelColor_eq_iff_sameAtomicType hx ((hlen x).trans hx)).1 (hχ' x).symm
    · intro m
      obtain ⟨r, rfl⟩ := exists_ratColor_eq m
      obtain ⟨s, hs⟩ := hchild x r
      exact ⟨ratColor s, x ++ [r], by simp [hx], (unravelVertex_append_singleton hx r).symm,
        by rw [hs, unravelVertex_append_singleton (by rw [hlen, hx])]⟩
    · intro m
      obtain ⟨s, rfl⟩ := exists_ratColor_eq m
      obtain ⟨r, hr⟩ := hchild' x s
      exact ⟨ratColor r, x ++ [r], by simp [hx], (unravelVertex_append_singleton hx r).symm,
        by rw [hr, unravelVertex_append_singleton (by rw [hlen, hx])]⟩
  have hP := (@potentialIso_iff_exists_isTupleBFSystem Language.graph _ ℕ ℕ c.toStructure
    d.toStructure).2 ⟨_, hS⟩
  exact isoSetoid_apply.2 <|
    (@countable_potentialIso_iff_iso Language.graph ℕ ℕ c.toStructure d.toStructure _ _).1 hP

/-- **Unravelling lemma, (i) ⇔ (ii).** For codes `c` and `d` of the language of
graphs, not necessarily simple graphs, `c` and `d` are isomorphic exactly when some order
automorphism `Φ` of `List ℚ` satisfies `χ_d ∘ Φ = χ_c`. -/
theorem isoSetoid_iff_exists_orderIso_unravelColor
    {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.graph ℕ c d ↔
      ∃ Φ : List ℚ ≃o List ℚ, unravelColor d ∘ Φ = unravelColor c := by
  refine ⟨fun h ↦ ?_, fun ⟨Φ, hΦ⟩ ↦ ?_⟩
  · obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
    obtain ⟨π, hπ⟩ := exists_orderIso_ratColor σ
    exact ⟨π.listCongr, funext fun x ↦ by simp [unravelColor_map hπ]⟩
  · have hlen (x : List ℚ) : (Φ x).length = x.length :=
      length_eq_of_unravelColor_eq (congrFun hΦ x)
    exact isoSetoid_of_perm_dropLast Φ.toEquiv (Φ.map_dropLast hlen) hΦ

/-- **Unravelling lemma, (i) ⇔ (iii).** For codes `c` and `d` of the language of graphs, not
necessarily simple graphs, `c` and `d` are isomorphic exactly when some bijection `Ψ` of
`List ℚ` preserving the parent `x ↦ x.dropLast` satisfies `χ_d ∘ Ψ = χ_c`. -/
theorem isoSetoid_iff_exists_perm_dropLast_unravelColor
    {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.graph ℕ c d ↔
      ∃ Ψ : Equiv.Perm (List ℚ), (∀ x, Ψ x.dropLast = (Ψ x).dropLast) ∧
        unravelColor d ∘ Ψ = unravelColor c := by
  refine ⟨fun h ↦ ?_, fun ⟨Ψ, hΨ, hχ⟩ ↦ isoSetoid_of_perm_dropLast Ψ hΨ hχ⟩
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  have hlen (x : List ℚ) : (Φ x).length = x.length :=
    length_eq_of_unravelColor_eq (congrFun hΦ x)
  exact ⟨Φ.toEquiv, Φ.map_dropLast hlen, hΦ⟩

end TauCeti.RelationalConfiguration
