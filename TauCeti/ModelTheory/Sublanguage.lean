/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Term.Symbols

/-!
# Symbol sublanguages and structure expansions

For a set `F` of function symbols and a set `R` of relation symbols of a language `L`, each
tagged by its arity, `symbSublang F R` is the sublanguage of `L` whose symbols are the members of
`F` and `R`, and `symbSublangIncl F R` is its inclusion into `L`. The inclusion is injective, the
sublanguage has countably many symbols of each sort when `F` and `R` are countable, and it is
relational whenever `L` is relational or `F` is empty. Nested symbol sets `F₁ ⊆ F₂` and `R₁ ⊆ R₂`
induce an injective inclusion `symbSublangMono hF hR` commuting with the inclusions into `L`.

Given a `(symbSublang F R)`-structure on `M` and `[Nonempty (L.Structure M)]`—which holds
automatically on every nonempty carrier (`nonempty_structure_of_nonempty`) and on arbitrary,
possibly empty carriers when `L` is relational (`nonempty_structure_of_isRelational`)—
`expandSymbStructure F R M` expands it to an `L`-structure on `M` by interpreting symbols outside
`F` using a chosen `L`-structure on `M` and relation symbols outside `R` as empty. The inclusion
`symbSublangIncl F R` is an expansion on `expandSymbStructure F R M`, and taking the reduct back
along `symbSublangIncl F R` recovers the given sublanguage structure.

A term of `L` whose function symbols lie in `F` restricts to the sublanguage
(`Term.restrictSymbols`), translating the restriction back along `symbSublangIncl F R` recovers the
term, and on any expansion along `symbSublangIncl F R` the restriction evaluates to the same
element as the term. If every symbol of `F` and `R` lies in the range of a language map
`g : L →ᴸ L'`, the inclusion factors through `g`; no injectivity of `g` is needed, since a preimage
is chosen for each symbol. The restriction of infinitary formulas and the generated symbol
sublanguages of formulas and sets of formulas live in `TauCeti.ModelTheory.Infinitary.Sublanguage`.

## Main definitions

* `FirstOrder.Language.symbSublang`: the sublanguage with the given symbols.
* `FirstOrder.Language.symbSublangIncl`: its inclusion into `L`, which is injective.
* `FirstOrder.Language.symbSublangMono`: the inclusion between nested symbol sublanguages.
* `FirstOrder.Language.expandSymbStructure`: expansion of a `(symbSublang F R)`-structure to an
  `L`-structure under `[Nonempty (L.Structure M)]`.
* `FirstOrder.Language.Term.restrictSymbols`: the restriction of a term to a sublanguage
  containing its function symbols.

## Main results

* `FirstOrder.Language.isExpansionOn_expandSymbStructure`: `symbSublangIncl F R` is an expansion on
  `expandSymbStructure F R M`.
* `FirstOrder.Language.reduct_expandSymbStructure`: the reduct of `expandSymbStructure F R M` along
  `symbSublangIncl F R` is the original `(symbSublang F R)`-structure.
* `FirstOrder.Language.Term.onTerm_restrictSymbols` and
  `FirstOrder.Language.Term.realize_restrictSymbols`: `symbSublangIncl F R` sends the restriction
  back to the term, preserving term evaluation in any expansion.
* `FirstOrder.Language.LHom.exists_comp_eq_symbSublangIncl`: the inclusion factors through any
  language map whose range contains the symbols.

## References

* `symbSublang`, `symbSublangIncl`, their countability and the restriction of terms follow
  `symbSublang`, `symbSublangIncl` and `Term.restrictSymbols` of `cameronfreer/infinitary-logic`
  at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/GeneratedSublanguage.lean`.
  Divergences from that source: the sublanguage lives in the universes of `L` rather than in
  `Language.{0, 0}`, and `symbSublangMono` and the factorization through a language map are new.
* `expandSymbStructure` and `isExpansionOn_expandSymbStructure` play the role of
  `InfinitaryLogic/Methods/SymbSublangExpansion.lean` in `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b` and parallel Mathlib's
  `FirstOrder.Language.LHom.defaultExpansion` and
  `FirstOrder.Language.LHom.Injective.isExpansionOn_default` in
  `Mathlib/ModelTheory/LanguageMap.lean`. Divergences: `expandSymbStructure` works for
  `L : Language.{u, v}` and `M : Type w` in arbitrary universes under `[Nonempty (L.Structure M)]`
  (covering both nonempty carriers and relational languages on possibly empty carriers without
  `Inhabited M` or decidability instances), interprets relation symbols outside `R` as empty
  without choice, and satisfies the exact round-trip `reduct_expandSymbStructure`.
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

/-! ### Monotonicity of symbol sublanguages -/

section Mono

variable {F₁ F₂ F₃ : Set (Σ n, L.Functions n)} {R₁ R₂ R₃ : Set (Σ n, L.Relations n)}

/-- The inclusion of a smaller symbol sublanguage into a larger one. -/
def symbSublangMono (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) :
    symbSublang F₁ R₁ →ᴸ symbSublang F₂ R₂ where
  onFunction _ f := ⟨f.1, hF f.2⟩
  onRelation _ r := ⟨r.1, hR r.2⟩

/-- `symbSublangMono` sends a function symbol to the same symbol of `L` with widened membership. -/
@[simp]
theorem symbSublangMono_onFunction (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) {n : ℕ}
    (f : (symbSublang F₁ R₁).Functions n) :
    (symbSublangMono hF hR).onFunction f = ⟨f.1, hF f.2⟩ :=
  (rfl)

/-- `symbSublangMono` sends a relation symbol to the same symbol of `L` with widened membership. -/
@[simp]
theorem symbSublangMono_onRelation (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) {n : ℕ}
    (r : (symbSublang F₁ R₁).Relations n) :
    (symbSublangMono hF hR).onRelation r = ⟨r.1, hR r.2⟩ :=
  (rfl)

/-- The inclusion between nested symbol sublanguages is injective. -/
theorem symbSublangMono_injective (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) :
    (symbSublangMono hF hR).Injective :=
  ⟨fun h => Subtype.ext (Subtype.mk.inj h), fun h => Subtype.ext (Subtype.mk.inj h)⟩

/-- Composing the outer inclusion into `L` with `symbSublangMono` gives the inner inclusion. -/
@[simp]
theorem symbSublangIncl_comp_symbSublangMono (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) :
    (symbSublangIncl F₂ R₂).comp (symbSublangMono hF hR) = symbSublangIncl F₁ R₁ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

/-- Along reflexive subset proofs, `symbSublangMono` is the identity language map. -/
@[simp]
theorem symbSublangMono_refl (hF : F ⊆ F) (hR : R ⊆ R) :
    symbSublangMono hF hR = LHom.id (symbSublang F R) :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

/-- Inclusions between symbol sublanguages compose to the transitive inclusion. -/
@[simp]
theorem symbSublangMono_comp (hF₂ : F₂ ⊆ F₃) (hR₂ : R₂ ⊆ R₃) (hF₁ : F₁ ⊆ F₂) (hR₁ : R₁ ⊆ R₂) :
    (symbSublangMono hF₂ hR₂).comp (symbSublangMono hF₁ hR₁) =
      symbSublangMono (hF₁.trans hF₂) (hR₁.trans hR₂) :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end Mono

/-! ### Expanding structures from symbol sublanguages -/

section Expand

variable (F R) (M : Type w) [Nonempty (L.Structure M)] [(symbSublang F R).Structure M]

/-- **Expanding a symbol-sublanguage structure to `L`.** Given a `(symbSublang F R)`-structure on
`M` and a witness that `M` carries at least one `L`-structure (automatic on any nonempty carrier
via `nonempty_structure_of_nonempty`, and on arbitrary—possibly empty—carriers when `L` is
relational via `nonempty_structure_of_isRelational`), `expandSymbStructure F R M` interprets
function and relation symbols in `F` and `R` as the sublanguage structure does, interprets function
symbols outside `F` using a chosen `L`-structure on `M`, and interprets relation symbols outside
`R` as empty. -/
@[instance_reducible]
noncomputable def expandSymbStructure : L.Structure M where
  funMap {n} f xs :=
    open Classical in
    if hf : ⟨n, f⟩ ∈ F then
      Structure.funMap (L := symbSublang F R) ⟨f, hf⟩ xs
    else
      (Classical.arbitrary (L.Structure M)).funMap f xs
  RelMap {n} r xs := ∃ hr : ⟨n, r⟩ ∈ R, Structure.RelMap (L := symbSublang F R) ⟨r, hr⟩ xs

variable {F R M}

/-- `expandSymbStructure` interprets each function symbol in `F` as the sublanguage structure
does. -/
@[simp]
theorem expandSymbStructure_funMap_of_mem {n : ℕ} {f : L.Functions n} (hf : ⟨n, f⟩ ∈ F)
    (xs : Fin n → M) :
    (expandSymbStructure F R M).funMap f xs =
      Structure.funMap (L := symbSublang F R) ⟨f, hf⟩ xs :=
  dite_eq_left hf

/-- In `expandSymbStructure`, a relation symbol holds of a tuple iff it lies in `R` and holds in
the sublanguage structure. -/
@[simp]
theorem expandSymbStructure_relMap_iff {n : ℕ} (r : L.Relations n) (xs : Fin n → M) :
    (expandSymbStructure F R M).RelMap r xs ↔
      ∃ hr : ⟨n, r⟩ ∈ R, Structure.RelMap (L := symbSublang F R) ⟨r, hr⟩ xs :=
  Iff.rfl

/-- `expandSymbStructure` interprets each relation symbol in `R` as the sublanguage structure
does. -/
theorem expandSymbStructure_relMap_of_mem {n : ℕ} {r : L.Relations n} (hr : ⟨n, r⟩ ∈ R)
    (xs : Fin n → M) :
    (expandSymbStructure F R M).RelMap r xs ↔
      Structure.RelMap (L := symbSublang F R) ⟨r, hr⟩ xs := by
  simp [hr]

/-- `expandSymbStructure` interprets every relation symbol outside `R` as empty. -/
theorem expandSymbStructure_relMap_of_notMem {n : ℕ} {r : L.Relations n} (hr : ⟨n, r⟩ ∉ R)
    (xs : Fin n → M) :
    ¬ (expandSymbStructure F R M).RelMap r xs := by
  simp [hr]

variable (F R M)

/-- The inclusion `symbSublangIncl F R` is an expansion on `expandSymbStructure F R M`. -/
instance isExpansionOn_expandSymbStructure :
    @LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M _
      (expandSymbStructure F R M) :=
  @LHom.IsExpansionOn.mk (symbSublang F R) L (symbSublangIncl F R) M _
    (expandSymbStructure F R M)
    (fun f xs => expandSymbStructure_funMap_of_mem f.2 xs)
    (fun r xs => propext (expandSymbStructure_relMap_of_mem r.2 xs))

/-- Restricting `expandSymbStructure F R M` back along `symbSublangIncl F R` recovers the original
`(symbSublang F R)`-structure. -/
@[simp]
theorem reduct_expandSymbStructure :
    @LHom.reduct (symbSublang F R) L (symbSublangIncl F R) M (expandSymbStructure F R M) =
      ‹(symbSublang F R).Structure M› := by
  refine Structure.ext (funext fun n => funext fun f => funext fun xs => ?_)
    (funext fun n => funext fun r => funext fun xs => ?_)
  · exact expandSymbStructure_funMap_of_mem f.2 xs
  · exact propext (expandSymbStructure_relMap_of_mem r.2 xs)

end Expand

/-! ### Restricting terms to symbol sublanguages -/

namespace Term

variable {α : Type uα}

/-- The subtype of function symbols occurring in a term is finite. -/
instance finite_functionsIn (t : L.Term α) : Finite t.functionsIn :=
  t.functionsIn_finite.to_subtype

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

/-- Translating a restricted term along `symbSublangMono` widens its symbol-set bounds. -/
@[simp]
theorem onTerm_symbSublangMono_restrictSymbols {F₁ F₂ : Set (Σ n, L.Functions n)}
    {R₁ R₂ : Set (Σ n, L.Relations n)} (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) (t : L.Term α)
    (ht : t.functionsIn ⊆ F₁) :
    (symbSublangMono hF hR).onTerm (t.restrictSymbols ht) = t.restrictSymbols (ht.trans hF) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [LHom.onTerm, ih]

/-- A symbol of `symbSublang F R` occurs in `t.restrictSymbols h` iff its underlying symbol of `L`
occurs in `t`. -/
@[simp]
theorem mem_functionsIn_restrictSymbols (t : L.Term α) (h : t.functionsIn ⊆ F)
    {s : Σ n, (symbSublang F R).Functions n} :
    s ∈ (t.restrictSymbols h).functionsIn ↔
      (⟨s.1, s.2.1⟩ : Σ n, L.Functions n) ∈ t.functionsIn := by
  conv_rhs => rw [← t.onTerm_restrictSymbols (R := R) h, functionsIn_onTerm]
  refine ⟨fun hs => ⟨s, hs, rfl⟩, ?_⟩
  rintro ⟨⟨k, f, hf⟩, hs, heq⟩
  rcases s with ⟨n, g, hg⟩
  cases heq
  exact hs

/-- On a carrier where the `L`-structure expands the `(symbSublang F R)`-structure along
`symbSublangIncl F R`, the restriction of a term evaluates to the same element as the term. -/
@[simp]
theorem realize_restrictSymbols {M : Type w} [L.Structure M] [(symbSublang F R).Structure M]
    [(symbSublangIncl F R).IsExpansionOn M] (t : L.Term α) (h : t.functionsIn ⊆ F) (v : α → M) :
    (t.restrictSymbols (R := R) h).realize v = t.realize v := by
  rw [← LHom.realize_onTerm (symbSublangIncl F R), onTerm_restrictSymbols]

/-- Evaluating a term whose function symbols lie in `F` inside `expandSymbStructure F R M` agrees
with evaluating its restriction in the `(symbSublang F R)`-structure. -/
theorem realize_expandSymbStructure {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] (t : L.Term α) (h : t.functionsIn ⊆ F) (v : α → M) :
    @realize L M (expandSymbStructure F R M) α v t = (t.restrictSymbols (R := R) h).realize v := by
  let := expandSymbStructure F R M
  exact (t.realize_restrictSymbols (R := R) h v).symm

/-- Two `L`-structures on `M` that both expand a common `(symbSublang F R)`-structure along
`symbSublangIncl F R` agree on every term whose occurring function symbols lie in `F`. -/
theorem realize_congr_of_isExpansionOn_symbSublangIncl {M : Type w}
    [S₀ : (symbSublang F R).Structure M] (S₁ S₂ : L.Structure M)
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₁]
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₂]
    (t : L.Term α) (h : t.functionsIn ⊆ F) (v : α → M) :
    @realize L M S₁ α v t = @realize L M S₂ α v t :=
  (@realize_restrictSymbols L F R α M S₁ S₀ _ t h v).symm.trans
    (@realize_restrictSymbols L F R α M S₂ S₀ _ t h v)

/-- Restricting an `L`-structure on `M` to `symbSublang F R` and re-expanding via
`expandSymbStructure F R M` preserves the value of every term whose occurring function symbols lie
in `F`. -/
theorem realize_expandSymbStructure_reduct {M : Type w} [L.Structure M] [Nonempty (L.Structure M)]
    (t : L.Term α) (h : t.functionsIn ⊆ F) (v : α → M) :
    @realize L M (@expandSymbStructure L F R M _ ((symbSublangIncl F R).reduct M)) α v t =
      t.realize v := by
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact t.realize_congr_of_isExpansionOn_symbSublangIncl (R := R) (expandSymbStructure F R M) _ h v

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
