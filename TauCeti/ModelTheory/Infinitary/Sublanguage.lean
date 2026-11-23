/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Symbols
public import TauCeti.ModelTheory.Sublanguage

/-!
# Infinitary formulas over symbol sublanguages and structure expansions

A formula of `L` whose occurring symbols lie in `F` and `R` restricts to the symbol sublanguage
`symbSublang F R` (`BoundedFormulaInf.restrictSymbols`), and translating the restriction back along
the inclusion `symbSublangIncl F R` recovers the formula. Truth is unaffected on any carrier where
the `L`-structure expands the `(symbSublang F R)`-structure along `symbSublangIncl F R`
(`BoundedFormulaInf.realize_restrictSymbols`, `SentenceInf.realize_restrictSymbols`): in
particular, both in the reduct of an `L`-structure and in `expandSymbStructure F R M`—which works
on every nonempty carrier and, when `L` is relational, on arbitrary (possibly empty) carriers. By
symbol locality, any two `L`-structures expanding a common `(symbSublang F R)`-structure give every
such formula the same truth value
(`BoundedFormulaInf.realize_congr_of_isExpansionOn_symbSublangIncl`), so restricting an
`L`-structure to `symbSublang F R` and re-expanding via `expandSymbStructure` preserves
satisfaction of all formulas whose symbols lie in `F` and `R`.

The occurrence sets of a single formula `φ` generate its own symbol sublanguage `φ.symbSublang`,
into which `φ` restricts as `φ.toSymbSublang` using every symbol of `φ.symbSublang`
(`functionsIn_toSymbSublang`, `relationsIn_toSymbSublang`); at a countable branching carrier `ι`
(such as `ℕ` for `L_{ω₁ω}`), `φ.symbSublang` has countably many function and relation symbols
regardless of the size of `L`. Likewise, a set `S` of formulas (in particular a set of `L_{ω₁ω}`
sentences) generates its symbol sublanguage `BoundedFormulaInf.setSymbSublang S` from the unions
`functionsInSet S` and `relationsInSet S`, restricts to `toSetSymbSublang S` using every symbol of
that sublanguage, and has countably many symbols whenever `ι` and `S` are countable. Together with
`expandSymbStructure` and `Language.smallPresentation`, this moves countable families of sentences
over arbitrary languages to countable languages in `Language.{0, 0}` and lifts models back to `L`.

The restriction also pulls formulas back along an arbitrary language map `g : L →ᴸ L'`: a formula
of `L'` whose occurring symbols all lie in the range of `g` is the image under `g` of a formula of
`L` (`LHom.exists_eq_onBoundedFormulaInf_of_subset_range`), without assuming `g` injective.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.restrictSymbols`: restriction of an infinitary formula to
  a symbol sublanguage containing its symbols.
* `FirstOrder.Language.BoundedFormulaInf.symbSublang` and
  `FirstOrder.Language.BoundedFormulaInf.toSymbSublang`: the symbol sublanguage of a single
  formula or sentence and the formula viewed in it.
* `FirstOrder.Language.BoundedFormulaInf.setSymbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.restrictSymbolsSet`, and
  `FirstOrder.Language.BoundedFormulaInf.toSetSymbSublang`: the symbol sublanguage and restriction
  of a set of formulas or sentences.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols`,
  `FirstOrder.Language.BoundedFormulaInf.realize_restrictSymbols`,
  `FirstOrder.Language.FormulaInf.realize_restrictSymbols`, and
  `FirstOrder.Language.SentenceInf.realize_restrictSymbols`: `symbSublangIncl F R` sends the
  restriction back to the formula and preserves realization along any expansion.
* `FirstOrder.Language.BoundedFormulaInf.realize_expandSymbStructure`,
  `FirstOrder.Language.FormulaInf.realize_expandSymbStructure`, and
  `FirstOrder.Language.SentenceInf.realize_expandSymbStructure`: realization in
  `expandSymbStructure F R M` agrees with realization of the restriction in the sublanguage
  structure, under `[Nonempty (L.Structure M)]`.
* `FirstOrder.Language.BoundedFormulaInf.realize_congr_of_isExpansionOn_symbSublangIncl` and
  `FirstOrder.Language.BoundedFormulaInf.realize_expandSymbStructure_reduct`: symbol locality
  across expansions of a common `(symbSublang F R)`-structure and under reduct-then-expand.
* `FirstOrder.Language.BoundedFormulaInf.functionsIn_toSymbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.relationsIn_toSymbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.functionsInSet_toSetSymbSublang`, and
  `FirstOrder.Language.BoundedFormulaInf.relationsInSet_toSetSymbSublang`: exact symbol generation
  for `φ.symbSublang` and `setSymbSublang S`.
* `FirstOrder.Language.BoundedFormulaInf.countable_functions_symbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.countable_relations_symbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.countable_functions_setSymbSublang`, and
  `FirstOrder.Language.BoundedFormulaInf.countable_relations_setSymbSublang`: countability of the
  symbol sublanguage of a formula and of a countable set of formulas at a countable carrier.
* `FirstOrder.Language.LHom.exists_eq_onBoundedFormulaInf_of_subset_range`: pullback of a formula
  whose symbols lie in the range of an arbitrary language map.

## References

* Formula restriction, generated sublanguages of sentences and countable theories, and realization
  transfer across `expandSymbStructure` follow `BoundedFormulaω.restrictSymbols` and the sublanguage
  reduction pattern in `InfinitaryLogic/Methods/GeneratedSublanguage.lean` and
  `InfinitaryLogic/Methods/SymbSublangExpansion.lean` of `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
  Divergences from that source: everything is generic in the branching carrier `ι` rather than
  specialized to `ℕ`, expansions work in arbitrary universes under `[Nonempty (L.Structure M)]`
  (covering relational languages on empty carriers as well as nonempty carriers), and the
  exact-generation equations `functionsIn_toSymbSublang`, `relationsIn_toSymbSublang`, and pullback
  along arbitrary language maps are new.
-/

public section

universe u v u' v' uα uι w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

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

/-- Restricting an included formula recovers the original formula. -/
@[simp]
theorem restrictSymbols_onBoundedFormulaInf {n : ℕ}
    (φ : (symbSublang F R).BoundedFormulaInf ι α n)
    (hF : ((symbSublangIncl F R).onBoundedFormulaInf φ).functionsIn ⊆ F)
    (hR : ((symbSublangIncl F R).onBoundedFormulaInf φ).relationsIn ⊆ R) :
    ((symbSublangIncl F R).onBoundedFormulaInf φ).restrictSymbols hF hR = φ :=
  (symbSublangIncl_injective F R).onBoundedFormulaInf_injective
    (onBoundedFormulaInf_restrictSymbols _ hF hR)

/-- Translating a restricted formula along `symbSublangInclusion` widens its symbol-set bounds. -/
@[simp]
theorem onBoundedFormulaInf_symbSublangInclusion_restrictSymbols
    {F₁ F₂ : Set (Σ k, L.Functions k)} {R₁ R₂ : Set (Σ k, L.Relations k)}
    (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF₁ : φ.functionsIn ⊆ F₁) (hR₁ : φ.relationsIn ⊆ R₁) :
    (symbSublangInclusion hF hR).onBoundedFormulaInf (φ.restrictSymbols hF₁ hR₁) =
      φ.restrictSymbols (hF₁.trans hF) (hR₁.trans hR) := by
  apply (symbSublangIncl_injective F₂ R₂).onBoundedFormulaInf_injective
  rw [← LHom.comp_onBoundedFormulaInf, symbSublangIncl_comp_symbSublangInclusion,
    onBoundedFormulaInf_restrictSymbols, onBoundedFormulaInf_restrictSymbols]

/-- A function symbol of `symbSublang F R` occurs in `φ.restrictSymbols hF hR` iff its underlying
symbol of `L` occurs in `φ`. -/
@[simp]
theorem mem_functionsIn_restrictSymbols {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    {s : Σ k, (symbSublang F R).Functions k} :
    s ∈ (φ.restrictSymbols hF hR).functionsIn ↔
      (⟨s.1, s.2.val⟩ : Σ k, L.Functions k) ∈ φ.functionsIn := by
  conv_rhs =>
    rw [← φ.onBoundedFormulaInf_restrictSymbols hF hR, LHom.functionsIn_onBoundedFormulaInf,
      ← symbSublangIncl_onFunction s.2]
  exact (Function.injective_id.sigma_map fun _ =>
    (symbSublangIncl_injective F R).onFunction).mem_set_image.symm

/-- A relation symbol of `symbSublang F R` occurs in `φ.restrictSymbols hF hR` iff its underlying
symbol of `L` occurs in `φ`. -/
@[simp]
theorem mem_relationsIn_restrictSymbols {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    {s : Σ k, (symbSublang F R).Relations k} :
    s ∈ (φ.restrictSymbols hF hR).relationsIn ↔
      (⟨s.1, s.2.val⟩ : Σ k, L.Relations k) ∈ φ.relationsIn := by
  conv_rhs =>
    rw [← φ.onBoundedFormulaInf_restrictSymbols hF hR, LHom.relationsIn_onBoundedFormulaInf,
      ← symbSublangIncl_onRelation s.2]
  exact (Function.injective_id.sigma_map fun _ =>
    (symbSublangIncl_injective F R).onRelation).mem_set_image.symm

/-! ### Realization across sublanguage expansions and symbol locality -/

/-- **Realization of a restriction.** On a carrier where the `L`-structure expands the structure
of the sublanguage along the inclusion, the restriction of a formula is realized exactly when the
formula is. This applies both to the reduct of an `L`-structure (`LHom.isExpansionOn_reduct`) and
to `expandSymbStructure F R M` (`isExpansionOn_expandSymbStructure`). -/
@[simp]
theorem realize_restrictSymbols {M : Type w} [L.Structure M] [(symbSublang F R).Structure M]
    [(symbSublangIncl F R).IsExpansionOn M] {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) (xs : Fin n → M) :
    (φ.restrictSymbols hF hR).Realize v xs ↔ φ.Realize v xs := by
  rw [← LHom.realize_onBoundedFormulaInf (symbSublangIncl F R), onBoundedFormulaInf_restrictSymbols]

/-- **Realization in `expandSymbStructure`.** Under `[Nonempty (L.Structure M)]` (in particular on
any nonempty carrier, or on any—possibly empty—carrier when `L` is relational), a formula whose
symbols lie in `F` and `R` is realized in `expandSymbStructure F R M` iff its restriction is
realized in the `(symbSublang F R)`-structure on `M`. -/
theorem realize_expandSymbStructure {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M (expandSymbStructure F R M) n φ v xs ↔
      (φ.restrictSymbols hF hR).Realize v xs := by
  let := expandSymbStructure F R M
  exact (φ.realize_restrictSymbols hF hR v xs).symm

/-- **Symbol locality across sublanguage expansions.** Any two `L`-structures on `M` that both
expand a common `(symbSublang F R)`-structure along `symbSublangIncl F R` agree on every formula
whose occurring symbols lie in `F` and `R`. -/
theorem realize_congr_of_isExpansionOn_symbSublangIncl {M : Type w}
    [S₀ : (symbSublang F R).Structure M] (S₁ S₂ : L.Structure M)
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₁]
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₂]
    {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M S₁ n φ v xs ↔ @Realize L ι α M S₂ n φ v xs :=
  (@realize_restrictSymbols L F R ι α M S₁ S₀ _ n φ hF hR v xs).symm.trans
    (@realize_restrictSymbols L F R ι α M S₂ S₀ _ n φ hF hR v xs)

/-- Restricting an `L`-structure on `M` to `symbSublang F R` and re-expanding via
`expandSymbStructure F R M` preserves the realization of every formula whose occurring symbols lie
in `F` and `R`. -/
theorem realize_expandSymbStructure_reduct {M : Type w} [S : L.Structure M]
    {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M (@expandSymbStructure L F R M ⟨S⟩ ((symbSublangIncl F R).reduct M)) n φ v xs ↔
      φ.Realize v xs := by
  have : Nonempty (L.Structure M) := ⟨S⟩
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact φ.realize_congr_of_isExpansionOn_symbSublangIncl (expandSymbStructure F R M) S hF hR v xs

/-! ### The symbol sublanguage of a single formula or sentence -/

/-- The **symbol sublanguage of a formula** (or sentence): the sublanguage of `L` generated by the
function and relation symbols occurring in `φ`. -/
protected abbrev symbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) : Language.{u, v} :=
  Language.symbSublang φ.functionsIn φ.relationsIn

/-- At a countable branching carrier, `φ.symbSublang` has countably many function symbols. Needed
as a dedicated instance because projecting `.Functions` on the reducible `Language.symbSublang`
erases `φ.relationsIn`, leaving an unassigned parameter in
`Language.countable_functions_symbSublang`. -/
protected instance countable_functions_symbSublang [Countable ι] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) : Countable (Σ k, φ.symbSublang.Functions k) :=
  Language.countable_functions_symbSublang

/-- At a countable branching carrier, `φ.symbSublang` has countably many relation symbols. Needed
as a dedicated instance because projecting `.Relations` on the reducible `Language.symbSublang`
erases `φ.functionsIn`, leaving an unassigned parameter in
`Language.countable_relations_symbSublang`. -/
protected instance countable_relations_symbSublang [Countable ι] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) : Countable (Σ k, φ.symbSublang.Relations k) :=
  Language.countable_relations_symbSublang

/-- The inclusion of `φ.symbSublang` into `L`. -/
protected abbrev symbSublangIncl {n : ℕ} (φ : L.BoundedFormulaInf ι α n) : φ.symbSublang →ᴸ L :=
  Language.symbSublangIncl φ.functionsIn φ.relationsIn

/-- The formula `φ` restricted to its own symbol sublanguage `φ.symbSublang`. -/
abbrev toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.symbSublang.BoundedFormulaInf ι α n :=
  φ.restrictSymbols subset_rfl subset_rfl

/-- Every function symbol of `φ.symbSublang` occurs in `φ.toSymbSublang`. -/
@[simp]
theorem functionsIn_toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.toSymbSublang.functionsIn = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (φ.mem_functionsIn_restrictSymbols subset_rfl subset_rfl).2 s.2.property

/-- Every relation symbol of `φ.symbSublang` occurs in `φ.toSymbSublang`. -/
@[simp]
theorem relationsIn_toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.toSymbSublang.relationsIn = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (φ.mem_relationsIn_restrictSymbols subset_rfl subset_rfl).2 s.2.property

/-! ### The symbol sublanguage of a set of formulas or sentences -/

section FormulaSet

variable {n : ℕ}

/-- The **symbol sublanguage of a set of formulas** (in particular, of a set of sentences): the
sublanguage of `L` generated by all function and relation symbols occurring in `S`. -/
abbrev setSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) : Language.{u, v} :=
  Language.symbSublang (functionsInSet S) (relationsInSet S)

/-- The inclusion of `setSymbSublang S` into `L`. -/
abbrev setSymbSublangIncl (S : Set (L.BoundedFormulaInf ι α n)) : setSymbSublang S →ᴸ L :=
  Language.symbSublangIncl (functionsInSet S) (relationsInSet S)

/-- At a countable branching carrier, `setSymbSublang S` has countably many function symbols for
any countable `S`. Needed as a dedicated instance because projecting `.Functions` on the reducible
`Language.symbSublang` erases `relationsInSet S`, leaving an unassigned parameter in
`Language.countable_functions_symbSublang`. -/
instance countable_functions_setSymbSublang [Countable ι]
    (S : Set (L.BoundedFormulaInf ι α n)) [Countable S] :
    Countable (Σ k, (setSymbSublang S).Functions k) :=
  Language.countable_functions_symbSublang

/-- At a countable branching carrier, `setSymbSublang S` has countably many relation symbols for
any countable `S`. Needed as a dedicated instance because projecting `.Relations` on the reducible
`Language.symbSublang` erases `functionsInSet S`, leaving an unassigned parameter in
`Language.countable_relations_symbSublang`. -/
instance countable_relations_setSymbSublang [Countable ι]
    (S : Set (L.BoundedFormulaInf ι α n)) [Countable S] :
    Countable (Σ k, (setSymbSublang S).Relations k) :=
  Language.countable_relations_symbSublang

/-- The restriction of every formula in `S` to a symbol sublanguage containing `functionsInSet S`
and `relationsInSet S`. -/
def restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    Set ((symbSublang F R).BoundedFormulaInf ι α n) :=
  Set.range fun φ : S =>
    φ.val.restrictSymbols ((Set.subset_biUnion_of_mem φ.property).trans hF)
      ((Set.subset_biUnion_of_mem φ.property).trans hR)

/-- Unfolding equation for `restrictSymbolsSet`. -/
theorem restrictSymbolsSet_def (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    restrictSymbolsSet S hF hR =
      Set.range fun φ : S =>
        φ.val.restrictSymbols ((Set.subset_biUnion_of_mem φ.property).trans hF)
          ((Set.subset_biUnion_of_mem φ.property).trans hR) :=
  (rfl)

/-- A formula in `symbSublang F R` lies in `restrictSymbolsSet S hF hR` iff its image under
`symbSublangIncl F R` lies in `S`. -/
@[simp]
theorem mem_restrictSymbolsSet_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {hF : functionsInSet S ⊆ F} {hR : relationsInSet S ⊆ R}
    {ψ : (symbSublang F R).BoundedFormulaInf ι α n} :
    ψ ∈ restrictSymbolsSet S hF hR ↔ (symbSublangIncl F R).onBoundedFormulaInf ψ ∈ S := by
  constructor
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    simpa only [onBoundedFormulaInf_restrictSymbols] using hφ
  · intro hψ
    refine ⟨⟨_, hψ⟩, (symbSublangIncl_injective F R).onBoundedFormulaInf_injective ?_⟩
    rw [onBoundedFormulaInf_restrictSymbols]

/-- Restricting a member `φ ∈ S` produces a member of `restrictSymbolsSet S hF hR`. -/
theorem restrictSymbols_mem_restrictSymbolsSet {S : Set (L.BoundedFormulaInf ι α n)}
    {hF : functionsInSet S ⊆ F} {hR : relationsInSet S ⊆ R}
    {φ : L.BoundedFormulaInf ι α n} (hφ : φ ∈ S)
    (hFφ : φ.functionsIn ⊆ F) (hRφ : φ.relationsIn ⊆ R) :
    φ.restrictSymbols hFφ hRφ ∈ restrictSymbolsSet S hF hR := by
  simp [hφ]

/-- Restricting the empty set of formulas gives the empty set. -/
@[simp]
theorem restrictSymbolsSet_empty
    (hF : functionsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) ⊆ F)
    (hR : relationsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) ⊆ R) :
    restrictSymbolsSet ∅ hF hR = ∅ := by
  ext ψ
  simp

/-- Restricting a singleton `{φ}` gives the singleton of `φ.restrictSymbols`. -/
@[simp]
theorem restrictSymbolsSet_singleton (φ : L.BoundedFormulaInf ι α n)
    (hF : functionsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) ⊆ F)
    (hR : relationsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) ⊆ R) :
    restrictSymbolsSet {φ} hF hR =
      {φ.restrictSymbols ((Set.biUnion_singleton φ _).symm.subset.trans hF)
        ((Set.biUnion_singleton φ _).symm.subset.trans hR)} := by
  ext ψ
  simp [← (symbSublangIncl_injective F R).onBoundedFormulaInf_injective.eq_iff]

/-- Restricting `insert φ S` inserts `φ.restrictSymbols` into the restriction of `S`. -/
@[simp]
theorem restrictSymbolsSet_insert (φ : L.BoundedFormulaInf ι α n)
    (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet (insert φ S) ⊆ F) (hR : relationsInSet (insert φ S) ⊆ R) :
    restrictSymbolsSet (insert φ S) hF hR =
      insert
        (φ.restrictSymbols ((Set.subset_biUnion_of_mem (Set.mem_insert φ S)).trans hF)
          ((Set.subset_biUnion_of_mem (Set.mem_insert φ S)).trans hR))
        (restrictSymbolsSet S
          ((Set.biUnion_subset_biUnion_left (Set.subset_insert φ S)).trans hF)
          ((Set.biUnion_subset_biUnion_left (Set.subset_insert φ S)).trans hR)) := by
  ext ψ
  simp [← (symbSublangIncl_injective F R).onBoundedFormulaInf_injective.eq_iff]

/-- Restricting a union of formula sets is the union of their restrictions. -/
@[simp]
theorem restrictSymbolsSet_union (S₁ S₂ : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet (S₁ ∪ S₂) ⊆ F) (hR : relationsInSet (S₁ ∪ S₂) ⊆ R) :
    restrictSymbolsSet (S₁ ∪ S₂) hF hR =
      restrictSymbolsSet S₁
        ((Set.biUnion_subset_biUnion_left Set.subset_union_left).trans hF)
        ((Set.biUnion_subset_biUnion_left Set.subset_union_left).trans hR) ∪
      restrictSymbolsSet S₂
        ((Set.biUnion_subset_biUnion_left Set.subset_union_right).trans hF)
        ((Set.biUnion_subset_biUnion_left Set.subset_union_right).trans hR) := by
  ext ψ
  simp

/-- `restrictSymbolsSet` is monotone in the set of formulas. -/
theorem restrictSymbolsSet_mono {S₁ S₂ : Set (L.BoundedFormulaInf ι α n)} (h : S₁ ⊆ S₂)
    {hF₁ : functionsInSet S₁ ⊆ F} {hR₁ : relationsInSet S₁ ⊆ R}
    {hF₂ : functionsInSet S₂ ⊆ F} {hR₂ : relationsInSet S₂ ⊆ R} :
    restrictSymbolsSet S₁ hF₁ hR₁ ⊆ restrictSymbolsSet S₂ hF₂ hR₂ :=
  fun _ hψ => mem_restrictSymbolsSet_iff.2 (h (mem_restrictSymbolsSet_iff.1 hψ))

/-- Translating `restrictSymbolsSet S hF hR` along `symbSublangIncl F R` recovers `S`. For
`T : L.Theoryω`, the left-hand side is
`(symbSublangIncl F R).onTheoryω (restrictSymbolsSet T hF hR)`. -/
@[simp]
theorem image_onBoundedFormulaInf_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    (symbSublangIncl F R).onBoundedFormulaInf '' restrictSymbolsSet S hF hR = S := by
  ext φ
  simp [restrictSymbolsSet_def, ← Set.range_comp]

/-- Restricting the image of a formula set under `symbSublangIncl F R` recovers the original
set. -/
@[simp]
theorem restrictSymbolsSet_image_onBoundedFormulaInf
    (S : Set ((symbSublang F R).BoundedFormulaInf ι α n))
    (hF : functionsInSet ((symbSublangIncl F R).onBoundedFormulaInf '' S) ⊆ F)
    (hR : relationsInSet ((symbSublangIncl F R).onBoundedFormulaInf '' S) ⊆ R) :
    restrictSymbolsSet ((symbSublangIncl F R).onBoundedFormulaInf '' S) hF hR = S := by
  ext ψ
  simp [(symbSublangIncl_injective F R).onBoundedFormulaInf_injective.mem_set_image]

/-- Translating `restrictSymbolsSet` along `symbSublangInclusion` widens its symbol-set bounds. -/
@[simp]
theorem image_onBoundedFormulaInf_symbSublangInclusion_restrictSymbolsSet
    {F₁ F₂ : Set (Σ k, L.Functions k)} {R₁ R₂ : Set (Σ k, L.Relations k)}
    (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) (S : Set (L.BoundedFormulaInf ι α n))
    (hF₁ : functionsInSet S ⊆ F₁) (hR₁ : relationsInSet S ⊆ R₁) :
    (symbSublangInclusion hF hR).onBoundedFormulaInf '' restrictSymbolsSet S hF₁ hR₁ =
      restrictSymbolsSet S (hF₁.trans hF) (hR₁.trans hR) := by
  ext ψ
  simp [restrictSymbolsSet_def, ← Set.range_comp]

/-- A function symbol of `symbSublang F R` occurs in `restrictSymbolsSet S hF hR` iff its
underlying symbol of `L` occurs in `S`. -/
theorem mem_functionsInSet_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    {s : Σ k, (symbSublang F R).Functions k} :
    s ∈ functionsInSet (restrictSymbolsSet S hF hR) ↔
      (⟨s.1, s.2.val⟩ : Σ k, L.Functions k) ∈ functionsInSet S := by
  conv_rhs =>
    rw [← image_onBoundedFormulaInf_restrictSymbolsSet S hF hR,
      LHom.functionsInSet_image_onBoundedFormulaInf, ← symbSublangIncl_onFunction s.2]
  exact (Function.injective_id.sigma_map fun _ =>
    (symbSublangIncl_injective F R).onFunction).mem_set_image.symm

/-- A relation symbol of `symbSublang F R` occurs in `restrictSymbolsSet S hF hR` iff its
underlying symbol of `L` occurs in `S`. -/
theorem mem_relationsInSet_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    {s : Σ k, (symbSublang F R).Relations k} :
    s ∈ relationsInSet (restrictSymbolsSet S hF hR) ↔
      (⟨s.1, s.2.val⟩ : Σ k, L.Relations k) ∈ relationsInSet S := by
  conv_rhs =>
    rw [← image_onBoundedFormulaInf_restrictSymbolsSet S hF hR,
      LHom.relationsInSet_image_onBoundedFormulaInf, ← symbSublangIncl_onRelation s.2]
  exact (Function.injective_id.sigma_map fun _ =>
    (symbSublangIncl_injective F R).onRelation).mem_set_image.symm

/-- Restricting a countable set of formulas gives a countable set of formulas in the sublanguage. -/
theorem countable_restrictSymbolsSet {S : Set (L.BoundedFormulaInf ι α n)} (hS : S.Countable)
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    (restrictSymbolsSet S hF hR).Countable := by
  have := hS.to_subtype
  exact Set.countable_range _

/-- The subtype of `restrictSymbolsSet S hF hR` is countable when `S` is countable. -/
instance (S : Set (L.BoundedFormulaInf ι α n)) [Countable S]
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    Countable (restrictSymbolsSet S hF hR) :=
  (countable_restrictSymbolsSet (Set.to_countable S) hF hR).to_subtype

/-- Along any expansion of `symbSublangIncl F R`, every formula in `restrictSymbolsSet S hF hR` is
realized at `(v, xs)` iff every formula in `S` is. -/
theorem forall_realize_restrictSymbolsSet_iff {M : Type w} [L.Structure M]
    [(symbSublang F R).Structure M] [(symbSublangIncl F R).IsExpansionOn M]
    (S : Set (L.BoundedFormulaInf ι α n)) (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    (v : α → M) (xs : Fin n → M) :
    (∀ ψ ∈ restrictSymbolsSet S hF hR, ψ.Realize v xs) ↔ ∀ φ ∈ S, φ.Realize v xs := by
  simp only [restrictSymbolsSet_def, Set.forall_mem_range, Subtype.forall, realize_restrictSymbols]

/-- In `expandSymbStructure F R M`, every formula in `S` is realized at `(v, xs)` iff every formula
in `restrictSymbolsSet S hF hR` is realized in the `(symbSublang F R)`-structure on `M`. -/
theorem forall_realize_expandSymbStructure_iff {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) (v : α → M) (xs : Fin n → M) :
    (∀ φ ∈ S, @Realize L ι α M (expandSymbStructure F R M) n φ v xs) ↔
      ∀ ψ ∈ restrictSymbolsSet S hF hR, ψ.Realize v xs := by
  let := expandSymbStructure F R M
  exact (forall_realize_restrictSymbolsSet_iff S hF hR v xs).symm

/-- The set `S` restricted to its own generated symbol sublanguage `setSymbSublang S`. -/
abbrev toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    Set ((setSymbSublang S).BoundedFormulaInf ι α n) :=
  restrictSymbolsSet S subset_rfl subset_rfl

/-- Every function symbol of `setSymbSublang S` occurs in `toSetSymbSublang S`. -/
@[simp]
theorem functionsInSet_toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (toSetSymbSublang S) = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (mem_functionsInSet_restrictSymbolsSet S subset_rfl subset_rfl).2 s.2.property

/-- Every relation symbol of `setSymbSublang S` occurs in `toSetSymbSublang S`. -/
@[simp]
theorem relationsInSet_toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (toSetSymbSublang S) = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (mem_relationsInSet_restrictSymbolsSet S subset_rfl subset_rfl).2 s.2.property

end FormulaSet

end BoundedFormulaInf

/-! ### Formula-level and sentence-level realization across sublanguages -/

namespace FormulaInf

variable {ι : Type uι} {α : Type uα}

/-- Along any expansion of `symbSublangIncl F R`, the restriction of an `L_{∞ω}` formula is
realized iff the formula is. -/
@[simp]
theorem realize_restrictSymbols {M : Type w} [L.Structure M] [(symbSublang F R).Structure M]
    [(symbSublangIncl F R).IsExpansionOn M] (φ : L.FormulaInf ι α)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) :
    FormulaInf.Realize (φ.restrictSymbols hF hR) v ↔ FormulaInf.Realize φ v := by
  simp only [FormulaInf.realize_def, BoundedFormulaInf.realize_restrictSymbols]

/-- An `L_{∞ω}` formula whose symbols lie in `F` and `R` is realized in `expandSymbStructure F R M`
iff its restriction is realized in the `(symbSublang F R)`-structure on `M`. -/
theorem realize_expandSymbStructure {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] (φ : L.FormulaInf ι α)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) :
    @FormulaInf.Realize L ι α M (expandSymbStructure F R M) φ v ↔
      FormulaInf.Realize (φ.restrictSymbols hF hR) v := by
  let := expandSymbStructure F R M
  exact (realize_restrictSymbols φ hF hR v).symm

/-- Two `L`-structures on `M` that both expand a common `(symbSublang F R)`-structure along
`symbSublangIncl F R` agree on every `L_{∞ω}` formula whose symbols lie in `F` and `R`. -/
theorem realize_congr_of_isExpansionOn_symbSublangIncl {M : Type w}
    [S₀ : (symbSublang F R).Structure M] (S₁ S₂ : L.Structure M)
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₁]
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₂]
    (φ : L.FormulaInf ι α) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) :
    @FormulaInf.Realize L ι α M S₁ φ v ↔ @FormulaInf.Realize L ι α M S₂ φ v :=
  (@realize_restrictSymbols L F R ι α M S₁ S₀ _ φ hF hR v).symm.trans
    (@realize_restrictSymbols L F R ι α M S₂ S₀ _ φ hF hR v)

/-- Restricting an `L`-structure on `M` to `symbSublang F R` and re-expanding via
`expandSymbStructure F R M` preserves the realization of every `L_{∞ω}` formula whose occurring
symbols lie in `F` and `R`. -/
theorem realize_expandSymbStructure_reduct {M : Type w} [S : L.Structure M]
    (φ : L.FormulaInf ι α) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) (v : α → M) :
    @FormulaInf.Realize L ι α M
        (@expandSymbStructure L F R M ⟨S⟩ ((symbSublangIncl F R).reduct M)) φ v ↔
      FormulaInf.Realize φ v := by
  have : Nonempty (L.Structure M) := ⟨S⟩
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact realize_congr_of_isExpansionOn_symbSublangIncl (expandSymbStructure F R M) S φ hF hR v

end FormulaInf

namespace SentenceInf

variable {ι : Type uι}

/-- Along any expansion of `symbSublangIncl F R`, the restriction of an `L_{∞ω}` sentence holds iff
the sentence does. -/
@[simp]
theorem realize_restrictSymbols {M : Type w} [L.Structure M] [(symbSublang F R).Structure M]
    [(symbSublangIncl F R).IsExpansionOn M] (φ : L.SentenceInf ι)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    SentenceInf.Realize (φ.restrictSymbols hF hR) M ↔ SentenceInf.Realize φ M := by
  rw [← LHom.realize_sentenceInf_onBoundedFormulaInf (symbSublangIncl F R),
    BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols]

/-- An `L_{∞ω}` sentence whose symbols lie in `F` and `R` holds in `expandSymbStructure F R M` iff
its restriction holds in the `(symbSublang F R)`-structure on `M`. -/
theorem realize_expandSymbStructure {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] (φ : L.SentenceInf ι)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    @SentenceInf.Realize L ι φ M (expandSymbStructure F R M) ↔
      SentenceInf.Realize (φ.restrictSymbols hF hR) M := by
  let := expandSymbStructure F R M
  exact (realize_restrictSymbols φ hF hR).symm

/-- Two `L`-structures on `M` that both expand a common `(symbSublang F R)`-structure along
`symbSublangIncl F R` satisfy the same sentences whose symbols lie in `F` and `R`. -/
theorem realize_congr_of_isExpansionOn_symbSublangIncl {M : Type w}
    [S₀ : (symbSublang F R).Structure M] (S₁ S₂ : L.Structure M)
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₁]
    [@LHom.IsExpansionOn (symbSublang F R) L (symbSublangIncl F R) M S₀ S₂]
    (φ : L.SentenceInf ι) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    @SentenceInf.Realize L ι φ M S₁ ↔ @SentenceInf.Realize L ι φ M S₂ :=
  (@realize_restrictSymbols L F R ι M S₁ S₀ _ φ hF hR).symm.trans
    (@realize_restrictSymbols L F R ι M S₂ S₀ _ φ hF hR)

/-- Restricting an `L`-structure on `M` to `symbSublang F R` and re-expanding via
`expandSymbStructure F R M` preserves the truth value of every sentence whose occurring symbols lie
in `F` and `R`. -/
theorem realize_expandSymbStructure_reduct {M : Type w} [S : L.Structure M]
    (φ : L.SentenceInf ι) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    @SentenceInf.Realize L ι φ M
        (@expandSymbStructure L F R M ⟨S⟩ ((symbSublangIncl F R).reduct M)) ↔
      SentenceInf.Realize φ M := by
  have : Nonempty (L.Structure M) := ⟨S⟩
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact realize_congr_of_isExpansionOn_symbSublangIncl (expandSymbStructure F R M) S φ hF hR

/-- Along any expansion of `symbSublangIncl F R`, every sentence in
`BoundedFormulaInf.restrictSymbolsSet S hF hR` holds in `M` iff every sentence in `S` does. -/
theorem forall_realize_restrictSymbolsSet_iff {M : Type w} [L.Structure M]
    [(symbSublang F R).Structure M] [(symbSublangIncl F R).IsExpansionOn M]
    (S : Set (L.SentenceInf ι)) (hF : BoundedFormulaInf.functionsInSet S ⊆ F)
    (hR : BoundedFormulaInf.relationsInSet S ⊆ R) :
    (∀ ψ ∈ (BoundedFormulaInf.restrictSymbolsSet S hF hR : Set ((symbSublang F R).SentenceInf ι)),
      SentenceInf.Realize ψ M) ↔ ∀ φ ∈ S, SentenceInf.Realize φ M := by
  simp only [BoundedFormulaInf.restrictSymbolsSet_def, Set.forall_mem_range, Subtype.forall,
    realize_restrictSymbols]

/-- In `expandSymbStructure F R M`, every sentence in `S` holds iff every sentence in
`BoundedFormulaInf.restrictSymbolsSet S hF hR` holds in the `(symbSublang F R)`-structure on `M`. -/
theorem forall_realize_expandSymbStructure_iff {M : Type w} [Nonempty (L.Structure M)]
    [(symbSublang F R).Structure M] (S : Set (L.SentenceInf ι))
    (hF : BoundedFormulaInf.functionsInSet S ⊆ F)
    (hR : BoundedFormulaInf.relationsInSet S ⊆ R) :
    (∀ φ ∈ S, @SentenceInf.Realize L ι φ M (expandSymbStructure F R M)) ↔
      ∀ ψ ∈ (BoundedFormulaInf.restrictSymbolsSet S hF hR : Set ((symbSublang F R).SentenceInf ι)),
        SentenceInf.Realize ψ M := by
  let := expandSymbStructure F R M
  exact (forall_realize_restrictSymbolsSet_iff S hF hR).symm

end SentenceInf

namespace LHom

variable {L' : Language.{u', v'}}

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
  refine ⟨h.onBoundedFormulaInf φ.toSymbSublang, ?_⟩
  rw [← comp_onBoundedFormulaInf, hh, BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols]

end LHom

end Language

end FirstOrder
