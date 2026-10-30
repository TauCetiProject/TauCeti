/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Symbols

/-!
# Symbol sublanguages

For a set `F` of function symbols and a set `R` of relation symbols of a language `L`, each
tagged by its arity, `symbSublang F R` is the sublanguage of `L` whose symbols are exactly the
members of `F` and `R`, and `symbSublangIncl F R` is its inclusion into `L`.

A formula of `L` whose occurring symbols lie in `F` and `R` restricts to the sublanguage
(`BoundedFormulaInf.restrictSymbols`), and translating the restriction back along the inclusion
recovers the formula. At a countable carrier a formula mentions only countably many symbols
(`BoundedFormulaInf.functionsIn_countable`), so the sublanguage of its own symbols has countably
many symbols of each sort, whatever the size of `L`. Truth is unaffected: the restriction is
realized in any structure on which the inclusion is an expansion, for instance in the reduct of an
`L`-structure, or in an `L`-structure expanding a structure of the sublanguage (Mathlib's
`LHom.defaultExpansion` with `symbSublangIncl_injective`), exactly when the formula is. This is how
statements proved for countable languages reach sentences of arbitrary languages.

The restriction also pulls formulas back along an arbitrary language map `g : L →ᴸ L'`: a formula
of `L'` whose occurring symbols all lie in the range of `g` is the image under `g` of a formula of
`L`. No injectivity of `g` is needed, since a preimage is chosen for each occurring symbol.

## Main definitions

* `FirstOrder.Language.symbSublang`: the sublanguage with the given symbols.
* `FirstOrder.Language.symbSublangIncl`: its inclusion, which is injective.
* `FirstOrder.Language.Term.restrictSymbols` and
  `FirstOrder.Language.BoundedFormulaInf.restrictSymbols`: the restriction of a term or an
  infinitary formula to a sublanguage containing its symbols.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols`: the inclusion sends
  the restriction back to the formula.
* `FirstOrder.Language.BoundedFormulaInf.realize_restrictSymbols`: the restriction is realized
  exactly when the formula is.
* `FirstOrder.Language.LHom.exists_eq_onBoundedFormulaInf_of_subset_range`: a formula whose symbols
  lie in the range of a language map is the image of a formula.

## References

* `symbSublang`, `symbSublangIncl`, their countability and the restriction of terms and formulas
  follow `symbSublang`, `symbSublangIncl`, `Term.restrictSymbols` and
  `BoundedFormulaω.restrictSymbols` of `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/GeneratedSublanguage.lean`.
  Divergences from that source: the sublanguage lives in the universes of `L` rather than in
  `Language.{0, 0}`, the restriction is defined at every carrier `ι` rather than at `ℕ`, and the
  realization of a restriction and the pullback along an arbitrary language map, obtained by
  factoring the inclusion through the map, are new.
-/

public section

universe u v u' v' uα uι w

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

namespace BoundedFormulaInf

variable {ι : Type uι} {α : Type uα}

/-- The restriction of an infinitary formula to a symbol sublanguage containing its function and
relation symbols. -/
def restrictSymbols : ∀ {n} (φ : L.BoundedFormulaInf ι α n), φ.functionsIn ⊆ F →
    φ.relationsIn ⊆ R → (symbSublang F R).BoundedFormulaInf ι α n
  | _, .falsum, _, _ => .falsum
  | _, .equal t₁ t₂, hF, _ =>
      .equal
        (t₁.restrictSymbols
          (Set.union_subset_iff.1 ((functionsIn_equal t₁ t₂).symm.subset.trans hF)).1)
        (t₂.restrictSymbols
          (Set.union_subset_iff.1 ((functionsIn_equal t₁ t₂).symm.subset.trans hF)).2)
  | _, .rel r ts, hF, hR =>
      .rel ⟨r, Set.singleton_subset_iff.1 ((relationsIn_rel r ts).symm.subset.trans hR)⟩ fun i =>
        (ts i).restrictSymbols
          (Set.iUnion_subset_iff.1 ((functionsIn_rel r ts).symm.subset.trans hF) i)
  | _, .imp φ ψ, hF, hR =>
      (φ.restrictSymbols (Set.union_subset_iff.1 ((functionsIn_imp φ ψ).symm.subset.trans hF)).1
          (Set.union_subset_iff.1 ((relationsIn_imp φ ψ).symm.subset.trans hR)).1).imp
        (ψ.restrictSymbols (Set.union_subset_iff.1 ((functionsIn_imp φ ψ).symm.subset.trans hF)).2
          (Set.union_subset_iff.1 ((relationsIn_imp φ ψ).symm.subset.trans hR)).2)
  | _, .all φ, hF, hR =>
      (φ.restrictSymbols ((functionsIn_all φ).symm.subset.trans hF)
        ((relationsIn_all φ).symm.subset.trans hR)).all
  | _, .iSup φs, hF, hR =>
      .iSup fun i => (φs i).restrictSymbols
        (Set.iUnion_subset_iff.1 ((functionsIn_iSup φs).symm.subset.trans hF) i)
        (Set.iUnion_subset_iff.1 ((relationsIn_iSup φs).symm.subset.trans hR) i)
  | _, .iInf φs, hF, hR =>
      .iInf fun i => (φs i).restrictSymbols
        (Set.iUnion_subset_iff.1 ((functionsIn_iInf φs).symm.subset.trans hF) i)
        (Set.iUnion_subset_iff.1 ((relationsIn_iInf φs).symm.subset.trans hR) i)

section ConstructorEqs

variable {n : ℕ}

/-- Restricting the false formula gives the false formula. -/
@[simp]
theorem restrictSymbols_falsum (hF : (falsum : L.BoundedFormulaInf ι α n).functionsIn ⊆ F)
    (hR : (falsum : L.BoundedFormulaInf ι α n).relationsIn ⊆ R) :
    (falsum.restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) = falsum :=
  (rfl)

/-- Restricting an equation restricts both sides. -/
@[simp]
theorem restrictSymbols_equal (t₁ t₂ : L.Term (α ⊕ Fin n))
    (hF : (equal t₁ t₂ : L.BoundedFormulaInf ι α n).functionsIn ⊆ F)
    (hR : (equal t₁ t₂ : L.BoundedFormulaInf ι α n).relationsIn ⊆ R) :
    ((equal t₁ t₂).restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      equal
        (t₁.restrictSymbols
          (Set.union_subset_iff.1 ((functionsIn_equal t₁ t₂).symm.subset.trans hF)).1)
        (t₂.restrictSymbols
          (Set.union_subset_iff.1 ((functionsIn_equal t₁ t₂).symm.subset.trans hF)).2) :=
  (rfl)

/-- Restricting a relational atom restricts the relation symbol and every argument. -/
@[simp]
theorem restrictSymbols_rel {l : ℕ} (r : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n))
    (hF : (rel r ts : L.BoundedFormulaInf ι α n).functionsIn ⊆ F)
    (hR : (rel r ts : L.BoundedFormulaInf ι α n).relationsIn ⊆ R) :
    ((rel r ts).restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      rel (⟨r, Set.singleton_subset_iff.1 ((relationsIn_rel r ts).symm.subset.trans hR)⟩ :
          (symbSublang F R).Relations l) fun i =>
        (ts i).restrictSymbols
          (Set.iUnion_subset_iff.1 ((functionsIn_rel r ts).symm.subset.trans hF) i) :=
  (rfl)

/-- Restriction commutes with implication. -/
@[simp]
theorem restrictSymbols_imp (φ ψ : L.BoundedFormulaInf ι α n) (hF : (φ.imp ψ).functionsIn ⊆ F)
    (hR : (φ.imp ψ).relationsIn ⊆ R) :
    ((φ.imp ψ).restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      (φ.restrictSymbols (Set.union_subset_iff.1 ((functionsIn_imp φ ψ).symm.subset.trans hF)).1
          (Set.union_subset_iff.1 ((relationsIn_imp φ ψ).symm.subset.trans hR)).1).imp
        (ψ.restrictSymbols (Set.union_subset_iff.1 ((functionsIn_imp φ ψ).symm.subset.trans hF)).2
          (Set.union_subset_iff.1 ((relationsIn_imp φ ψ).symm.subset.trans hR)).2) :=
  (rfl)

/-- Restriction commutes with universal quantification. -/
@[simp]
theorem restrictSymbols_all (φ : L.BoundedFormulaInf ι α (n + 1)) (hF : φ.all.functionsIn ⊆ F)
    (hR : φ.all.relationsIn ⊆ R) :
    (φ.all.restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      (φ.restrictSymbols ((functionsIn_all φ).symm.subset.trans hF)
        ((relationsIn_all φ).symm.subset.trans hR)).all :=
  (rfl)

/-- Restriction commutes with disjunctions over the carrier. -/
@[simp]
theorem restrictSymbols_iSup (φs : ι → L.BoundedFormulaInf ι α n)
    (hF : (iSup φs).functionsIn ⊆ F) (hR : (iSup φs).relationsIn ⊆ R) :
    ((iSup φs).restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      .iSup fun i => (φs i).restrictSymbols
        (Set.iUnion_subset_iff.1 ((functionsIn_iSup φs).symm.subset.trans hF) i)
        (Set.iUnion_subset_iff.1 ((relationsIn_iSup φs).symm.subset.trans hR) i) :=
  (rfl)

/-- Restriction commutes with conjunctions over the carrier. -/
@[simp]
theorem restrictSymbols_iInf (φs : ι → L.BoundedFormulaInf ι α n)
    (hF : (iInf φs).functionsIn ⊆ F) (hR : (iInf φs).relationsIn ⊆ R) :
    ((iInf φs).restrictSymbols hF hR : (symbSublang F R).BoundedFormulaInf ι α n) =
      .iInf fun i => (φs i).restrictSymbols
        (Set.iUnion_subset_iff.1 ((functionsIn_iInf φs).symm.subset.trans hF) i)
        (Set.iUnion_subset_iff.1 ((relationsIn_iInf φs).symm.subset.trans hR) i) :=
  (rfl)

end ConstructorEqs

/-- The inclusion sends the restriction of a formula back to the formula. -/
@[simp]
theorem onBoundedFormulaInf_restrictSymbols {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    (symbSublangIncl F R).onBoundedFormulaInf (φ.restrictSymbols hF hR) = φ := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel r ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- **Realization of a restriction.** On a carrier where the `L`-structure expands the structure
of the sublanguage along the inclusion, the restriction of a formula is realized exactly when the
formula is. This applies to the reduct of an `L`-structure, through Mathlib's
`LHom.isExpansionOn_reduct`. -/
@[simp]
theorem realize_restrictSymbols {M : Type w} [L.Structure M] [(symbSublang F R).Structure M]
    [(symbSublangIncl F R).IsExpansionOn M] {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) (xs : Fin n → M) :
    (φ.restrictSymbols hF hR).Realize v xs ↔ φ.Realize v xs := by
  rw [← LHom.realize_onBoundedFormulaInf (symbSublangIncl F R), onBoundedFormulaInf_restrictSymbols]

end BoundedFormulaInf

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

/-- **Pulling a formula back along a language map.** An infinitary formula of `L'` whose occurring
function and relation symbols all lie in the range of `g : L →ᴸ L'` is the image under `g` of a
formula of `L`. No injectivity of `g` is needed. -/
theorem exists_eq_onBoundedFormulaInf_of_subset_range (g : L →ᴸ L') {ι : Type uι} {α : Type uα}
    {n : ℕ} (φ : L'.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆
      Set.range fun s : Σ n, L.Functions n => (⟨s.1, g.onFunction s.2⟩ : Σ k, L'.Functions k))
    (hR : φ.relationsIn ⊆
      Set.range fun s : Σ n, L.Relations n => (⟨s.1, g.onRelation s.2⟩ : Σ k, L'.Relations k)) :
    ∃ ψ : L.BoundedFormulaInf ι α n, g.onBoundedFormulaInf ψ = φ := by
  obtain ⟨h, hh⟩ := g.exists_comp_eq_symbSublangIncl hF hR
  refine ⟨h.onBoundedFormulaInf (φ.restrictSymbols subset_rfl subset_rfl), ?_⟩
  rw [← comp_onBoundedFormulaInf, hh, BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols]

end LHom

end Language

end FirstOrder
