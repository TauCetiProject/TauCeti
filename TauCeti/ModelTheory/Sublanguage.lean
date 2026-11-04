/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Term.Symbols

/-!
# Symbol sublanguages

For a set `F` of function symbols and a set `R` of relation symbols of a language `L`, each
tagged by its arity, `symbSublang F R` is the sublanguage of `L` whose symbols are exactly the
members of `F` and `R`, and `symbSublangIncl F R` is its inclusion into `L`. The inclusion is
injective, and the sublanguage has countably many symbols of each sort when `F` and `R` are
countable.

A term of `L` whose function symbols lie in `F` restricts to the sublanguage
(`Term.restrictSymbols`), and translating the restriction back along the inclusion recovers the
term. If every symbol of `F` and `R` lies in the range of a language map `g : L →ᴸ L'`, the
inclusion factors through `g`; no injectivity of `g` is needed, since a preimage is chosen for each
symbol. The restriction of infinitary formulas lives in
`TauCeti.ModelTheory.Infinitary.Sublanguage`.

## Main definitions

* `FirstOrder.Language.symbSublang`: the sublanguage with the given symbols.
* `FirstOrder.Language.symbSublangIncl`: its inclusion, which is injective.
* `FirstOrder.Language.Term.restrictSymbols`: the restriction of a term to a sublanguage
  containing its function symbols.

## Main results

* `FirstOrder.Language.Term.onTerm_restrictSymbols`: the inclusion sends the restriction back to
  the term.
* `FirstOrder.Language.LHom.exists_comp_eq_symbSublangIncl`: the inclusion factors through any
  language map whose range contains the symbols.

## References

* `symbSublang`, `symbSublangIncl`, their countability and the restriction of terms follow
  `symbSublang`, `symbSublangIncl` and `Term.restrictSymbols` of `cameronfreer/infinitary-logic`
  at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/GeneratedSublanguage.lean`.
  Divergences from that source: the sublanguage lives in the universes of `L` rather than in
  `Language.{0, 0}`, and the factorization through a language map is new.
-/

public section

universe u v u' v' uα

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
