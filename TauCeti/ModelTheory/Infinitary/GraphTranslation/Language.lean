/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Basic.Countable.Basic

/-!
# The graph language of a first-order language

The graph language `L.graphLanguage` has no function symbols. Its relation symbols are those of
`L`, at their arities, together with one `(k + 1)`-ary relation symbol `G_f` for each `k`-ary
function symbol `f` of `L`, standing for the graph `f(x₀, …, x_{k-1}) = y` of `f`. Every
`L`-structure becomes an `L.graphLanguage`-structure on the same carrier, its graph expansion
`graphExpansion L M`.

Formulas of `L` translate into formulas of the graph language with the same realization in the
graph expansion (`TauCeti.ModelTheory.Infinitary.GraphTranslation.Relationalize`). This is how
statements proved for relational languages, in which every closed term of a constant expansion is
a constant, reach languages with function symbols.

The relation symbols of the graph language coming from given sets `F` of function symbols and `R`
of relation symbols of `L` form the set `relSym F R`. The two kinds of graph-language symbols are
disjoint, so `relSym` commutes with intersections: the symbols shared by two translated formulas
are the translations of the symbols shared by the two formulas (`relSym_inter`).

## Main definitions

* `FirstOrder.Language.GraphRelation`: the relation symbols of the graph language.
* `FirstOrder.Language.graphLanguage`: the graph language, which is relational.
* `FirstOrder.Language.graphExpansion`: the graph expansion of an `L`-structure.
* `FirstOrder.Language.baseRelSym`, `FirstOrder.Language.graphRelSym`: the graph-language symbol
  of a relation symbol and of a function symbol of `L`, as arity-tagged symbols.
* `FirstOrder.Language.relSym`: the graph-language symbols coming from sets of symbols of `L`.

## Main results

* `FirstOrder.Language.baseRelSym_injective`, `FirstOrder.Language.graphRelSym_injective` and
  `FirstOrder.Language.baseRelSym_ne_graphRelSym`: the two symbol maps are injective with disjoint
  images.
* `FirstOrder.Language.relSym_inter`: the shared-vocabulary identity
  `relSym F₁ R₁ ∩ relSym F₂ R₂ = relSym (F₁ ∩ F₂) (R₁ ∩ R₂)`, with the laws `relSym_union` and
  `relSym_iUnion`.

## References

* The graph language, its expansion, the symbol maps and `relSym` follow `GraphRelation`,
  `graphLanguage`, `graphExpansion`, `baseRelSym`, `graphRelSym` and `relSym` of
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/Interpolation/GraphLanguage.lean`.
  Divergences from that source: the graph language lives in the universes of `L` rather than in
  `Language.{0, 0}`, and the graph expansion is defined on carriers in any universe.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- The relation symbols of the graph language of `L`: every relation symbol of `L` is kept at its
arity (`base`), and every `k`-ary function symbol of `L` gives a `(k + 1)`-ary relation symbol
(`graph`) for its graph. -/
inductive GraphRelation : ℕ → Type (max u v)
  /-- A relation symbol of `L`, kept at its arity. -/
  | base {n : ℕ} (R : L.Relations n) : GraphRelation n
  /-- The graph of a `k`-ary function symbol of `L`, a `(k + 1)`-ary relation symbol whose last
  argument is the value. -/
  | graph {k : ℕ} (f : L.Functions k) : GraphRelation (k + 1)

/-- The **graph language** of `L`: no function symbols, and as relation symbols those of `L`
together with the graph of each function symbol of `L`. The definition is reducible, so that a
relation symbol of the graph language is built and taken apart as a `GraphRelation`. -/
abbrev graphLanguage : Language.{u, max u v} where
  Functions _ := PEmpty
  Relations := L.GraphRelation

instance isRelational_graphLanguage : L.graphLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty PEmpty)

variable {L}

/-- The graph-language symbol of an arity-tagged relation symbol of `L`. -/
def baseRelSym (R : Σ n, L.Relations n) : Σ n, L.GraphRelation n :=
  ⟨R.1, .base R.2⟩

/-- The graph-language symbol of an arity-tagged function symbol of `L`: the graph relation, of
arity one more. -/
def graphRelSym (f : Σ n, L.Functions n) : Σ n, L.GraphRelation n :=
  ⟨f.1 + 1, .graph f.2⟩

@[simp]
theorem baseRelSym_mk {n : ℕ} (R : L.Relations n) :
    baseRelSym ⟨n, R⟩ = ⟨n, GraphRelation.base R⟩ := (rfl)

@[simp]
theorem graphRelSym_mk {n : ℕ} (f : L.Functions n) :
    graphRelSym ⟨n, f⟩ = ⟨n + 1, GraphRelation.graph f⟩ := (rfl)

theorem baseRelSym_injective : Function.Injective (baseRelSym (L := L)) := by
  rintro ⟨n, R⟩ ⟨n', R'⟩ h
  simp only [baseRelSym_mk, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

theorem graphRelSym_injective : Function.Injective (graphRelSym (L := L)) := by
  rintro ⟨n, f⟩ ⟨n', f'⟩ h
  simp only [graphRelSym_mk, Sigma.mk.injEq, Nat.add_right_cancel_iff] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

theorem baseRelSym_ne_graphRelSym (R : Σ n, L.Relations n) (f : Σ n, L.Functions n) :
    baseRelSym R ≠ graphRelSym f := by
  obtain ⟨n, R⟩ := R
  obtain ⟨k, f⟩ := f
  intro h
  simp only [baseRelSym_mk, graphRelSym_mk, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h

/-- A graph-language symbol is the symbol of a relation symbol or of a function symbol of `L`. -/
theorem baseRelSym_or_graphRelSym (S : Σ n, L.GraphRelation n) :
    (∃ R, baseRelSym R = S) ∨ ∃ f, graphRelSym f = S := by
  obtain ⟨_, R | f⟩ := S
  · exact Or.inl ⟨⟨_, R⟩, rfl⟩
  · exact Or.inr ⟨⟨_, f⟩, rfl⟩

/-- The graph language has countably many relation symbols when `L` has countably many symbols of
both sorts. -/
instance countable_relations_graphLanguage [Countable (Σ n, L.Functions n)]
    [Countable (Σ n, L.Relations n)] : Countable (Σ n, L.graphLanguage.Relations n) := by
  have : Function.Surjective (Sum.elim (baseRelSym (L := L)) graphRelSym) := fun S => by
    obtain ⟨R, hR⟩ | ⟨f, hf⟩ := baseRelSym_or_graphRelSym S
    · exact ⟨Sum.inl R, hR⟩
    · exact ⟨Sum.inr f, hf⟩
  exact this.countable

/-! ### The symbols coming from sets of symbols of `L` -/

/-- The relation symbols of the graph language coming from a set `F` of function symbols and a set
`R` of relation symbols of `L`: the base symbols of `R` and the graph symbols of `F`. -/
def relSym (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    Set (Σ n, L.GraphRelation n) :=
  baseRelSym '' R ∪ graphRelSym '' F

theorem relSym_def (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    relSym F R = baseRelSym '' R ∪ graphRelSym '' F := (rfl)

@[simp]
theorem baseRelSym_mem_relSym {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {r : Σ n, L.Relations n} : baseRelSym r ∈ relSym F R ↔ r ∈ R := by
  rw [relSym, Set.mem_union, baseRelSym_injective.mem_set_image, or_iff_left]
  rintro ⟨f, -, h⟩
  exact baseRelSym_ne_graphRelSym r f h.symm

@[simp]
theorem graphRelSym_mem_relSym {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {f : Σ n, L.Functions n} : graphRelSym f ∈ relSym F R ↔ f ∈ F := by
  rw [relSym, Set.mem_union, graphRelSym_injective.mem_set_image, or_iff_right]
  rintro ⟨r, -, h⟩
  exact baseRelSym_ne_graphRelSym r f h

/-- `baseRelSym_mem_relSym` for the raw pair, the simp normal form of `baseRelSym ⟨n, r⟩`. -/
@[simp]
theorem mk_base_mem_relSym {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {n : ℕ} {r : L.Relations n} :
    (⟨n, GraphRelation.base r⟩ : Σ n, L.GraphRelation n) ∈ relSym F R ↔ ⟨n, r⟩ ∈ R :=
  baseRelSym_mem_relSym (r := ⟨n, r⟩)

/-- `graphRelSym_mem_relSym` for the raw pair, the simp normal form of `graphRelSym ⟨n, f⟩`. -/
@[simp]
theorem mk_graph_mem_relSym {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {n : ℕ} {f : L.Functions n} :
    (⟨n + 1, GraphRelation.graph f⟩ : Σ n, L.GraphRelation n) ∈ relSym F R ↔ ⟨n, f⟩ ∈ F :=
  graphRelSym_mem_relSym (f := ⟨n, f⟩)

@[simp]
theorem relSym_empty :
    relSym (∅ : Set (Σ n, L.Functions n)) (∅ : Set (Σ n, L.Relations n)) = ∅ := by
  simp [relSym]

theorem relSym_union (F₁ F₂ : Set (Σ n, L.Functions n)) (R₁ R₂ : Set (Σ n, L.Relations n)) :
    relSym (F₁ ∪ F₂) (R₁ ∪ R₂) = relSym F₁ R₁ ∪ relSym F₂ R₂ := by
  simp only [relSym, Set.image_union]
  exact Set.union_union_union_comm _ _ _ _

theorem relSym_iUnion {κ : Sort*} (F : κ → Set (Σ n, L.Functions n))
    (R : κ → Set (Σ n, L.Relations n)) :
    relSym (⋃ i, F i) (⋃ i, R i) = ⋃ i, relSym (F i) (R i) := by
  simp only [relSym, Set.image_iUnion]
  exact (Set.iUnion_union_distrib _ _).symm

/-- **The shared-vocabulary identity**: the graph-language symbols coming from two pairs of symbol
sets meet exactly in the symbols coming from the shared symbols. -/
theorem relSym_inter (F₁ F₂ : Set (Σ n, L.Functions n)) (R₁ R₂ : Set (Σ n, L.Relations n)) :
    relSym F₁ R₁ ∩ relSym F₂ R₂ = relSym (F₁ ∩ F₂) (R₁ ∩ R₂) := by
  ext S
  obtain ⟨R, rfl⟩ | ⟨f, rfl⟩ := baseRelSym_or_graphRelSym S <;> simp

/-! ### The graph expansion -/

variable (L) (M : Type w) [L.Structure M]

/-- The **graph expansion** of an `L`-structure: relation symbols of `L` keep their
interpretation, and the graph relation of `f` holds of `(x₀, …, x_{k-1}, y)` exactly when
`f(x₀, …, x_{k-1}) = y`. The graph language has no function symbols to interpret. -/
@[instance_reducible]
def graphExpansion : L.graphLanguage.Structure M where
  funMap f := PEmpty.elim f
  RelMap
    | .base R, xs => Structure.RelMap R xs
    | .graph f, xs => Structure.funMap f (Fin.init xs) = xs (Fin.last _)

variable {L M}

@[simp]
theorem graphExpansion_relMap_base {n : ℕ} (R : L.Relations n) (xs : Fin n → M) :
    (graphExpansion L M).RelMap (GraphRelation.base R) xs ↔ Structure.RelMap R xs :=
  Iff.rfl

@[simp]
theorem graphExpansion_relMap_graph {k : ℕ} (f : L.Functions k) (xs : Fin (k + 1) → M) :
    (graphExpansion L M).RelMap (GraphRelation.graph f) xs ↔
      Structure.funMap f (Fin.init xs) = xs (Fin.last k) :=
  Iff.rfl

end Language

end FirstOrder
