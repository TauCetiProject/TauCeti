/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Term.Symbols

/-!
# Symbol sublanguages

For a set `F` of function symbols and a set `R` of relation symbols of a language `L`, each
tagged by its arity, `symbSublang F R` is the sublanguage of `L` whose symbols are exactly the
members of `F` and `R`, and `symbSublangIncl F R` is its inclusion into `L`. The inclusion is
injective, the sublanguage has countably many symbols of each sort when `F` and `R` are
countable, and it is relational whenever `L` is relational or `F` is empty.

A term of `L` whose function symbols lie in `F` restricts to the sublanguage
(`Term.restrictSymbols`), and translating the restriction back along the inclusion recovers the
term. If every symbol of `F` and `R` lies in the range of a language map `g : L →ᴸ L'`, the
inclusion factors through `g`; no injectivity of `g` is needed, since a preimage is chosen for each
symbol. The restriction of infinitary formulas lives in
`TauCeti.ModelTheory.Infinitary.Sublanguage`.

Conversely, a structure of the sublanguage expands to an `L`-structure on the same carrier
(`expandSymbStructure`), interpreting the symbols outside `F` and `R` as some `L`-structure on the
carrier does. Such a structure exists on every nonempty carrier, and on every carrier at all when
`L` is relational, so the expansion needs no nonemptiness for relational languages. The inclusion is
an expansion on it, so a formula whose symbols lie in `F` and `R` has the same truth value in the
expansion as its restriction has in the sublanguage structure. This is how a model found for a
sublanguage becomes a model of the original language.

## Main definitions

* `FirstOrder.Language.symbSublang`: the sublanguage with the given symbols.
* `FirstOrder.Language.symbSublangIncl`: its inclusion, which is injective.
* `FirstOrder.Language.Term.restrictSymbols`: the restriction of a term to a sublanguage
  containing its function symbols.
* `FirstOrder.Language.expandSymbStructure`: the expansion of a structure of the sublanguage to
  an `L`-structure on the same carrier.

## Main results

* `FirstOrder.Language.Term.onTerm_restrictSymbols`: the inclusion sends the restriction back to
  the term.
* `FirstOrder.Language.LHom.exists_comp_eq_symbSublangIncl`: the inclusion factors through any
  language map whose range contains the symbols.
* `FirstOrder.Language.isExpansionOn_expandSymbStructure`: the inclusion is an expansion on the
  expanded structure.

## References

* `symbSublang`, `symbSublangIncl`, their countability and the restriction of terms follow
  `symbSublang`, `symbSublangIncl` and `Term.restrictSymbols` of `cameronfreer/infinitary-logic`
  at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/GeneratedSublanguage.lean`.
  Divergences from that source: the sublanguage lives in the universes of `L` rather than in
  `Language.{0, 0}`, and the factorization through a language map is new.
* `expandSymbStructure` is modelled on Mathlib's `LHom.defaultExpansion`; the corresponding
  expansion of `cameronfreer/infinitary-logic` at the same commit is in
  `InfinitaryLogic/Methods/SymbSublangExpansion.lean`. Divergence: the symbols outside the
  sublanguage are interpreted through an arbitrary `L`-structure on the carrier rather than by a
  default element, so that no element is needed for relational languages.
-/

public section

universe u v u' v' uα w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- The **symbol sublanguage** of `L` whose function and relation symbols of each arity are the
members of `F` and `R`. The definition is reducible: a symbol of the sublanguage is a symbol of `L`
together with a proof of membership, and is built and taken apart as such. -/
abbrev symbSublang (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    Language.{u, v} where
  Functions n := {f : L.Functions n // ⟨n, f⟩ ∈ F}
  Relations n := {r : L.Relations n // ⟨n, r⟩ ∈ R}

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

variable (F R) in
/-- The inclusion of a symbol sublanguage into `L`. -/
def symbSublangIncl : symbSublang F R →ᴸ L where
  onFunction _ f := f.1
  onRelation _ r := r.1

/-- The inclusion sends a function symbol of the sublanguage to the underlying symbol of `L`. -/
@[simp]
theorem symbSublangIncl_onFunction {n : ℕ} (f : (symbSublang F R).Functions n) :
    (symbSublangIncl F R).onFunction f = f.1 :=
  (rfl)

/-- The inclusion sends a relation symbol of the sublanguage to the underlying symbol of `L`. -/
@[simp]
theorem symbSublangIncl_onRelation {n : ℕ} (r : (symbSublang F R).Relations n) :
    (symbSublangIncl F R).onRelation r = r.1 :=
  (rfl)

variable (F R) in
/-- The inclusion of a symbol sublanguage is injective. -/
theorem symbSublangIncl_injective : (symbSublangIncl F R).Injective :=
  ⟨fun h => Subtype.val_injective h, fun h => Subtype.val_injective h⟩

/-- A symbol sublanguage with countably many function symbols has countably many function
symbols, counted over all arities. -/
instance countable_functions_symbSublang [Countable F] :
    Countable (Σ n, (symbSublang F R).Functions n) :=
  Function.Injective.countable (f := fun s : Σ n, (symbSublang F R).Functions n =>
      (⟨⟨s.1, s.2.1⟩, s.2.2⟩ : F)) <| by
    rintro ⟨n, f, hf⟩ ⟨m, f', hf'⟩ h
    cases congrArg Subtype.val h
    rfl

/-- A symbol sublanguage with countably many relation symbols has countably many relation
symbols, counted over all arities. -/
instance countable_relations_symbSublang [Countable R] :
    Countable (Σ n, (symbSublang F R).Relations n) :=
  Function.Injective.countable (f := fun s : Σ n, (symbSublang F R).Relations n =>
      (⟨⟨s.1, s.2.1⟩, s.2.2⟩ : R)) <| by
    rintro ⟨n, r, hr⟩ ⟨m, r', hr'⟩ h
    cases congrArg Subtype.val h
    rfl

/-- Any symbol sublanguage of a relational language is relational. -/
instance isRelational_symbSublang [L.IsRelational] : (symbSublang F R).IsRelational :=
  fun _ => ⟨fun f => isEmptyElim f.1⟩

/-- A symbol sublanguage with an empty set of function symbols is relational. -/
instance isRelational_symbSublang_of_isEmpty [IsEmpty F] : (symbSublang F R).IsRelational :=
  fun n => ⟨fun f => isEmptyElim (⟨⟨n, f.1⟩, f.2⟩ : F)⟩

section Expansion

variable (F R) (M : Type w) [(symbSublang F R).Structure M] [Nonempty (L.Structure M)]

open scoped Classical in
/-- **The expansion of a structure of a symbol sublanguage.** On a carrier `M` carrying some
`L`-structure, a structure of `symbSublang F R` expands to the `L`-structure that interprets the
symbols of `F` and `R` as the sublanguage does and every other symbol as an arbitrarily chosen
`L`-structure on `M` does. Some `L`-structure exists on every nonempty carrier
(`nonempty_structure_of_nonempty`) and, for relational `L`, on every carrier
(`nonempty_structure_of_isRelational`). The inclusion `symbSublangIncl F R` is an expansion on the
result (`isExpansionOn_expandSymbStructure`). -/
@[instance_reducible]
noncomputable def expandSymbStructure : L.Structure M :=
  let S : L.Structure M := Classical.choice ‹_›
  { funMap := fun {n} f xs =>
      if h : ⟨n, f⟩ ∈ F then Structure.funMap (L := symbSublang F R) ⟨f, h⟩ xs else S.funMap f xs
    RelMap := fun {n} r xs =>
      if h : ⟨n, r⟩ ∈ R then Structure.RelMap (L := symbSublang F R) ⟨r, h⟩ xs else S.RelMap r xs }

/-- The inclusion of a symbol sublanguage is an expansion on the expansion of any structure of the
sublanguage. -/
instance isExpansionOn_expandSymbStructure :
    @LHom.IsExpansionOn _ _ (symbSublangIncl F R) M _ (expandSymbStructure F R M) :=
  letI := expandSymbStructure F R M
  ⟨fun f _ => dite_eq_left f.2, fun r _ => dite_eq_left r.2⟩

end Expansion

namespace Term

variable {α : Type uα}

/-- The restriction of a term to a symbol sublanguage containing its function symbols. -/
def restrictSymbols : ∀ t : L.Term α, t.functionsIn ⊆ F → (symbSublang F R).Term α
  | var a, _ => var a
  | func f ts, h =>
      func ⟨f, Set.singleton_subset_iff.1
          (Set.union_subset_iff.1 ((functionsIn_func f ts).symm.subset.trans h)).1⟩ fun i =>
        restrictSymbols (ts i) (Set.iUnion_subset_iff.1
          (Set.union_subset_iff.1 ((functionsIn_func f ts).symm.subset.trans h)).2 i)

/-- Restricting a variable gives the same variable. -/
@[simp]
theorem restrictSymbols_var (a : α) (h : (var a : L.Term α).functionsIn ⊆ F) :
    ((var a).restrictSymbols h : (symbSublang F R).Term α) = var a :=
  (rfl)

/-- Restricting an application restricts the function symbol and every argument. -/
@[simp]
theorem restrictSymbols_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term α)
    (h : (func f ts).functionsIn ⊆ F) :
    ((func f ts).restrictSymbols h : (symbSublang F R).Term α) =
      func (⟨f, Set.singleton_subset_iff.1
          (Set.union_subset_iff.1 ((functionsIn_func f ts).symm.subset.trans h)).1⟩ :
          (symbSublang F R).Functions n) fun i =>
        (ts i).restrictSymbols (Set.iUnion_subset_iff.1
          (Set.union_subset_iff.1 ((functionsIn_func f ts).symm.subset.trans h)).2 i) :=
  (rfl)

/-- The inclusion sends the restriction of a term back to the term. -/
@[simp]
theorem onTerm_restrictSymbols (t : L.Term α) (h : t.functionsIn ⊆ F) :
    (symbSublangIncl F R).onTerm (t.restrictSymbols h) = t := by
  induction t with
  | var => rfl
  | func f ts ih => simp [LHom.onTerm, ih]

end Term

namespace LHom

variable {L' : Language.{u', v'}}

/-- If every symbol of `F` and `R` is the image of a symbol under `g`, the inclusion of the
symbol sublanguage factors through `g`. -/
theorem exists_comp_eq_symbSublangIncl (g : L →ᴸ L') {F : Set (Σ n, L'.Functions n)}
    {R : Set (Σ n, L'.Relations n)}
    (hF : F ⊆
      Set.range fun s : Σ n, L.Functions n => (⟨s.1, g.onFunction s.2⟩ : Σ k, L'.Functions k))
    (hR : R ⊆
      Set.range fun s : Σ n, L.Relations n => (⟨s.1, g.onRelation s.2⟩ : Σ k, L'.Relations k)) :
    ∃ h : symbSublang F R →ᴸ L, g.comp h = symbSublangIncl F R := by
  have hF' : ∀ n (f : (symbSublang F R).Functions n), ∃ f₀ : L.Functions n,
      g.onFunction f₀ = f.1 := by
    rintro n ⟨f, hf⟩
    obtain ⟨⟨k, f₀⟩, hk⟩ := hF hf
    cases hk
    exact ⟨f₀, rfl⟩
  have hR' : ∀ n (r : (symbSublang F R).Relations n), ∃ r₀ : L.Relations n,
      g.onRelation r₀ = r.1 := by
    rintro n ⟨r, hr⟩
    obtain ⟨⟨k, r₀⟩, hk⟩ := hR hr
    cases hk
    exact ⟨r₀, rfl⟩
  choose fF hfF using hF'
  choose fR hfR using hR'
  exact ⟨⟨fun _ => fF _, fun _ => fR _⟩,
    LHom.funext (funext fun n => funext (hfF n)) (funext fun n => funext (hfR n))⟩

end LHom

end Language

end FirstOrder
