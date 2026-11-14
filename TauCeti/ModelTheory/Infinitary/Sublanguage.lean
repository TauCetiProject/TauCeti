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
* `FirstOrder.Language.BoundedFormulaInf.functionsInSet`,
  `FirstOrder.Language.BoundedFormulaInf.relationsInSet`,
  `FirstOrder.Language.BoundedFormulaInf.setSymbSublang`,
  `FirstOrder.Language.BoundedFormulaInf.restrictSymbolsSet`, and
  `FirstOrder.Language.BoundedFormulaInf.toSetSymbSublang`: the symbol sublanguage and restriction
  of a set of formulas or sentences.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols`,
  `FirstOrder.Language.BoundedFormulaInf.realize_restrictSymbols`, and
  `FirstOrder.Language.SentenceInf.realize_restrictSymbols`: `symbSublangIncl F R` sends the
  restriction back to the formula and preserves realization along any expansion.
* `FirstOrder.Language.BoundedFormulaInf.realize_expandSymbStructure` and
  `FirstOrder.Language.SentenceInf.realize_expandSymbStructure`: realization in
  `expandSymbStructure F R M` agrees with realization of the restriction in the sublanguage
  structure, under `[Nonempty (L.Structure M)]`.
* `FirstOrder.Language.BoundedFormulaInf.realize_congr_of_isExpansionOn_symbSublangIncl` and
  `FirstOrder.Language.BoundedFormulaInf.realize_expandSymbStructure_reduct`: symbol locality
  across expansions of a common `(symbSublang F R)`-structure and under reduct-then-expand.
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

/-- Translating a restricted formula along `symbSublangMono` widens its symbol-set bounds. -/
@[simp]
theorem onBoundedFormulaInf_symbSublangMono_restrictSymbols
    {F₁ F₂ : Set (Σ k, L.Functions k)} {R₁ R₂ : Set (Σ k, L.Relations k)}
    (hF : F₁ ⊆ F₂) (hR : R₁ ⊆ R₂) {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF₁ : φ.functionsIn ⊆ F₁) (hR₁ : φ.relationsIn ⊆ R₁) :
    (symbSublangMono hF hR).onBoundedFormulaInf (φ.restrictSymbols hF₁ hR₁) =
      φ.restrictSymbols (hF₁.trans hF) (hR₁.trans hR) := by
  apply (symbSublangIncl_injective F₂ R₂).onBoundedFormulaInf_injective
  rw [← LHom.comp_onBoundedFormulaInf, symbSublangIncl_comp_symbSublangMono,
    onBoundedFormulaInf_restrictSymbols, onBoundedFormulaInf_restrictSymbols]

/-- A function symbol of `symbSublang F R` occurs in `φ.restrictSymbols hF hR` iff its underlying
symbol of `L` occurs in `φ`. -/
@[simp]
theorem mem_functionsIn_restrictSymbols {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    {s : Σ k, (symbSublang F R).Functions k} :
    s ∈ (φ.restrictSymbols hF hR).functionsIn ↔
      (⟨s.1, s.2.1⟩ : Σ k, L.Functions k) ∈ φ.functionsIn := by
  conv_rhs =>
    rw [← φ.onBoundedFormulaInf_restrictSymbols hF hR, LHom.functionsIn_onBoundedFormulaInf]
  refine ⟨fun hs => ⟨s, hs, by simp⟩, ?_⟩
  rintro ⟨⟨k, f, hf⟩, hs, heq⟩
  simp only [symbSublangIncl_onFunction] at heq
  rcases s with ⟨m, g, hg⟩
  cases heq
  exact hs

/-- A relation symbol of `symbSublang F R` occurs in `φ.restrictSymbols hF hR` iff its underlying
symbol of `L` occurs in `φ`. -/
@[simp]
theorem mem_relationsIn_restrictSymbols {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    {s : Σ k, (symbSublang F R).Relations k} :
    s ∈ (φ.restrictSymbols hF hR).relationsIn ↔
      (⟨s.1, s.2.1⟩ : Σ k, L.Relations k) ∈ φ.relationsIn := by
  conv_rhs =>
    rw [← φ.onBoundedFormulaInf_restrictSymbols hF hR, LHom.relationsIn_onBoundedFormulaInf]
  refine ⟨fun hs => ⟨s, hs, by simp⟩, ?_⟩
  rintro ⟨⟨k, r, hr⟩, hs, heq⟩
  simp only [symbSublangIncl_onRelation] at heq
  rcases s with ⟨m, q, hq⟩
  cases heq
  exact hs

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
theorem realize_expandSymbStructure_reduct {M : Type w} [L.Structure M] [Nonempty (L.Structure M)]
    {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M (@expandSymbStructure L F R M _ ((symbSublangIncl F R).reduct M)) n φ v xs ↔
      φ.Realize v xs := by
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact φ.realize_congr_of_isExpansionOn_symbSublangIncl (expandSymbStructure F R M) _ hF hR v xs

/-! ### The symbol sublanguage of a single formula or sentence -/

/-- At a countable branching carrier, the subtype of function symbols occurring in a formula is
countable. -/
instance countable_functionsIn [Countable ι] {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    Countable φ.functionsIn :=
  φ.functionsIn_countable.to_subtype

/-- At a countable branching carrier, the subtype of relation symbols occurring in a formula is
countable. -/
instance countable_relationsIn [Countable ι] {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    Countable φ.relationsIn :=
  φ.relationsIn_countable.to_subtype

/-- The **symbol sublanguage of a formula** (or sentence): the sublanguage of `L` generated by the
function and relation symbols occurring in `φ`. -/
protected abbrev symbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) : Language.{u, v} :=
  Language.symbSublang φ.functionsIn φ.relationsIn

/-- At a countable branching carrier, `φ.symbSublang` has countably many function symbols. -/
protected instance countable_functions_symbSublang [Countable ι] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) : Countable (Σ k, φ.symbSublang.Functions k) :=
  Language.countable_functions_symbSublang

/-- At a countable branching carrier, `φ.symbSublang` has countably many relation symbols. -/
protected instance countable_relations_symbSublang [Countable ι] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) : Countable (Σ k, φ.symbSublang.Relations k) :=
  Language.countable_relations_symbSublang

/-- The inclusion of `φ.symbSublang` into `L`. -/
protected abbrev symbSublangIncl {n : ℕ} (φ : L.BoundedFormulaInf ι α n) : φ.symbSublang →ᴸ L :=
  Language.symbSublangIncl φ.functionsIn φ.relationsIn

/-- The formula `φ` restricted to its own symbol sublanguage `φ.symbSublang`. -/
def toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.symbSublang.BoundedFormulaInf ι α n :=
  φ.restrictSymbols subset_rfl subset_rfl

/-- Unfolding equation for `BoundedFormulaInf.toSymbSublang`. -/
theorem toSymbSublang_def {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.toSymbSublang = φ.restrictSymbols subset_rfl subset_rfl :=
  (rfl)

/-- Translating `φ.toSymbSublang` along `φ.symbSublangIncl` recovers `φ`. -/
@[simp]
theorem onBoundedFormulaInf_toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.symbSublangIncl.onBoundedFormulaInf φ.toSymbSublang = φ :=
  φ.onBoundedFormulaInf_restrictSymbols subset_rfl subset_rfl

/-- Every function symbol of `φ.symbSublang` occurs in `φ.toSymbSublang`. -/
@[simp]
theorem functionsIn_toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.toSymbSublang.functionsIn = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (φ.mem_functionsIn_restrictSymbols subset_rfl subset_rfl).2 s.2.2

/-- Every relation symbol of `φ.symbSublang` occurs in `φ.toSymbSublang`. -/
@[simp]
theorem relationsIn_toSymbSublang {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    φ.toSymbSublang.relationsIn = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (φ.mem_relationsIn_restrictSymbols subset_rfl subset_rfl).2 s.2.2

/-- Along any expansion of `φ.symbSublangIncl`, `φ.toSymbSublang` is realized iff `φ` is. -/
@[simp]
theorem realize_toSymbSublang {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) [φ.symbSublang.Structure M]
    [φ.symbSublangIncl.IsExpansionOn M] (v : α → M) (xs : Fin n → M) :
    φ.toSymbSublang.Realize v xs ↔ φ.Realize v xs :=
  φ.realize_restrictSymbols subset_rfl subset_rfl v xs

/-- Expanding a `φ.symbSublang`-structure on `M` via `expandSymbStructure` realizes `φ` iff the
`φ.symbSublang`-structure realizes `φ.toSymbSublang`. -/
theorem realize_expandSymbStructure_toSymbSublang {M : Type w} [Nonempty (L.Structure M)]
    {n : ℕ} (φ : L.BoundedFormulaInf ι α n) [φ.symbSublang.Structure M]
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M (expandSymbStructure φ.functionsIn φ.relationsIn M) n φ v xs ↔
      φ.toSymbSublang.Realize v xs :=
  φ.realize_expandSymbStructure subset_rfl subset_rfl v xs

/-! ### The symbol sublanguage of a set of formulas or sentences -/

section FormulaSet

variable {n : ℕ}

/-- The arity-tagged function symbols occurring in at least one formula of `S`. -/
def functionsInSet (S : Set (L.BoundedFormulaInf ι α n)) : Set (Σ k, L.Functions k) :=
  ⋃ φ ∈ S, φ.functionsIn

/-- The arity-tagged relation symbols occurring in at least one formula of `S`. -/
def relationsInSet (S : Set (L.BoundedFormulaInf ι α n)) : Set (Σ k, L.Relations k) :=
  ⋃ φ ∈ S, φ.relationsIn

/-- Unfolding equation for `functionsInSet`. -/
theorem functionsInSet_def (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet S = ⋃ φ ∈ S, φ.functionsIn :=
  (rfl)

/-- Unfolding equation for `relationsInSet`. -/
theorem relationsInSet_def (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet S = ⋃ φ ∈ S, φ.relationsIn :=
  (rfl)

/-- No function symbols occur in the empty set of formulas. -/
@[simp]
theorem functionsInSet_empty :
    functionsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) = ∅ := by
  simp [functionsInSet_def]

/-- No relation symbols occur in the empty set of formulas. -/
@[simp]
theorem relationsInSet_empty :
    relationsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) = ∅ := by
  simp [relationsInSet_def]

/-- The function symbols of a singleton `{φ}` are those of `φ`. -/
@[simp]
theorem functionsInSet_singleton (φ : L.BoundedFormulaInf ι α n) :
    functionsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) = φ.functionsIn := by
  simp [functionsInSet_def]

/-- The relation symbols of a singleton `{φ}` are those of `φ`. -/
@[simp]
theorem relationsInSet_singleton (φ : L.BoundedFormulaInf ι α n) :
    relationsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) = φ.relationsIn := by
  simp [relationsInSet_def]

/-- Inserting a formula adds its occurring function symbols. -/
@[simp]
theorem functionsInSet_insert (φ : L.BoundedFormulaInf ι α n)
    (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (insert φ S) = φ.functionsIn ∪ functionsInSet S := by
  simp [functionsInSet_def]

/-- Inserting a formula adds its occurring relation symbols. -/
@[simp]
theorem relationsInSet_insert (φ : L.BoundedFormulaInf ι α n)
    (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (insert φ S) = φ.relationsIn ∪ relationsInSet S := by
  simp [relationsInSet_def]

/-- The function symbols of a union of formula sets are the union of their function symbols. -/
@[simp]
theorem functionsInSet_union (S₁ S₂ : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (S₁ ∪ S₂) = functionsInSet S₁ ∪ functionsInSet S₂ := by
  rw [functionsInSet_def, Set.biUnion_union]
  rfl

/-- The relation symbols of a union of formula sets are the union of their relation symbols. -/
@[simp]
theorem relationsInSet_union (S₁ S₂ : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (S₁ ∪ S₂) = relationsInSet S₁ ∪ relationsInSet S₂ := by
  rw [relationsInSet_def, Set.biUnion_union]
  rfl

/-- Every member of `S` has its occurring function symbols in `functionsInSet S`. -/
theorem subset_functionsInSet_of_mem {φ : L.BoundedFormulaInf ι α n}
    {S : Set (L.BoundedFormulaInf ι α n)} (hφ : φ ∈ S) :
    φ.functionsIn ⊆ functionsInSet S :=
  Set.subset_biUnion_of_mem hφ

/-- Every member of `S` has its occurring relation symbols in `relationsInSet S`. -/
theorem subset_relationsInSet_of_mem {φ : L.BoundedFormulaInf ι α n}
    {S : Set (L.BoundedFormulaInf ι α n)} (hφ : φ ∈ S) :
    φ.relationsIn ⊆ relationsInSet S :=
  Set.subset_biUnion_of_mem hφ

/-- `functionsInSet` is monotone in the set of formulas. -/
theorem functionsInSet_mono {S₁ S₂ : Set (L.BoundedFormulaInf ι α n)} (h : S₁ ⊆ S₂) :
    functionsInSet S₁ ⊆ functionsInSet S₂ :=
  Set.biUnion_mono h fun _ _ => subset_rfl

/-- `relationsInSet` is monotone in the set of formulas. -/
theorem relationsInSet_mono {S₁ S₂ : Set (L.BoundedFormulaInf ι α n)} (h : S₁ ⊆ S₂) :
    relationsInSet S₁ ⊆ relationsInSet S₂ :=
  Set.biUnion_mono h fun _ _ => subset_rfl

/-- At a countable branching carrier, a countable set of formulas mentions only countably many
function symbols. -/
theorem functionsInSet_countable [Countable ι] {S : Set (L.BoundedFormulaInf ι α n)}
    (hS : S.Countable) : (functionsInSet S).Countable :=
  hS.biUnion fun φ _ => φ.functionsIn_countable

/-- At a countable branching carrier, a countable set of formulas mentions only countably many
relation symbols. -/
theorem relationsInSet_countable [Countable ι] {S : Set (L.BoundedFormulaInf ι α n)}
    (hS : S.Countable) : (relationsInSet S).Countable :=
  hS.biUnion fun φ _ => φ.relationsIn_countable

/-- At a countable branching carrier, `functionsInSet S` is countable for any countable `S`. -/
instance countable_functionsInSet [Countable ι] (S : Set (L.BoundedFormulaInf ι α n))
    [Countable S] : Countable (functionsInSet S) :=
  (functionsInSet_countable (Set.to_countable S)).to_subtype

/-- At a countable branching carrier, `relationsInSet S` is countable for any countable `S`. -/
instance countable_relationsInSet [Countable ι] (S : Set (L.BoundedFormulaInf ι α n))
    [Countable S] : Countable (relationsInSet S) :=
  (relationsInSet_countable (Set.to_countable S)).to_subtype

/-- The **symbol sublanguage of a set of formulas** (in particular, of a set of sentences): the
sublanguage of `L` generated by all function and relation symbols occurring in `S`. -/
abbrev setSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) : Language.{u, v} :=
  Language.symbSublang (functionsInSet S) (relationsInSet S)

/-- The inclusion of `setSymbSublang S` into `L`. -/
abbrev setSymbSublangIncl (S : Set (L.BoundedFormulaInf ι α n)) : setSymbSublang S →ᴸ L :=
  Language.symbSublangIncl (functionsInSet S) (relationsInSet S)

/-- At a countable branching carrier, `setSymbSublang S` has countably many function symbols for
any countable `S`. -/
instance countable_functions_setSymbSublang [Countable ι]
    (S : Set (L.BoundedFormulaInf ι α n)) [Countable S] :
    Countable (Σ k, (setSymbSublang S).Functions k) :=
  Language.countable_functions_symbSublang

/-- At a countable branching carrier, `setSymbSublang S` has countably many relation symbols for
any countable `S`. -/
instance countable_relations_setSymbSublang [Countable ι]
    (S : Set (L.BoundedFormulaInf ι α n)) [Countable S] :
    Countable (Σ k, (setSymbSublang S).Relations k) :=
  Language.countable_relations_symbSublang

/-- A countable set of formulas at a countable carrier generates a symbol sublanguage with
countably many function symbols. -/
theorem countable_functions_setSymbSublang_of_countable [Countable ι]
    {S : Set (L.BoundedFormulaInf ι α n)} (hS : S.Countable) :
    Countable (Σ k, (setSymbSublang S).Functions k) := by
  have := hS.to_subtype
  infer_instance

/-- A countable set of formulas at a countable carrier generates a symbol sublanguage with
countably many relation symbols. -/
theorem countable_relations_setSymbSublang_of_countable [Countable ι]
    {S : Set (L.BoundedFormulaInf ι α n)} (hS : S.Countable) :
    Countable (Σ k, (setSymbSublang S).Relations k) := by
  have := hS.to_subtype
  infer_instance

/-- The restriction of every formula in `S` to a symbol sublanguage containing `functionsInSet S`
and `relationsInSet S`. -/
def restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    Set ((symbSublang F R).BoundedFormulaInf ι α n) :=
  Set.range fun φ : S =>
    φ.1.restrictSymbols ((subset_functionsInSet_of_mem φ.2).trans hF)
      ((subset_relationsInSet_of_mem φ.2).trans hR)

/-- Membership characterization for `restrictSymbolsSet`. -/
@[simp]
theorem mem_restrictSymbolsSet_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {hF : functionsInSet S ⊆ F} {hR : relationsInSet S ⊆ R}
    {ψ : (symbSublang F R).BoundedFormulaInf ι α n} :
    ψ ∈ restrictSymbolsSet S hF hR ↔
      ∃ (φ : L.BoundedFormulaInf ι α n) (hφ : φ ∈ S),
        φ.restrictSymbols ((subset_functionsInSet_of_mem hφ).trans hF)
          ((subset_relationsInSet_of_mem hφ).trans hR) = ψ :=
  Subtype.exists

/-- Restricting a member `φ ∈ S` produces a member of `restrictSymbolsSet S hF hR`. -/
theorem restrictSymbols_mem_restrictSymbolsSet {S : Set (L.BoundedFormulaInf ι α n)}
    {hF : functionsInSet S ⊆ F} {hR : relationsInSet S ⊆ R}
    {φ : L.BoundedFormulaInf ι α n} (hφ : φ ∈ S)
    (hFφ : φ.functionsIn ⊆ F) (hRφ : φ.relationsIn ⊆ R) :
    φ.restrictSymbols hFφ hRφ ∈ restrictSymbolsSet S hF hR :=
  ⟨⟨φ, hφ⟩, rfl⟩

/-- Translating `restrictSymbolsSet S hF hR` along `symbSublangIncl F R` recovers `S`. For
`T : L.Theoryω`, the left-hand side is
`(symbSublangIncl F R).onTheoryω (restrictSymbolsSet T hF hR)`. -/
@[simp]
theorem image_onBoundedFormulaInf_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    (symbSublangIncl F R).onBoundedFormulaInf '' restrictSymbolsSet S hF hR = S := by
  ext φ
  simp [restrictSymbolsSet, ← Set.range_comp]

/-- A function symbol of `symbSublang F R` occurs in `restrictSymbolsSet S hF hR` iff its
underlying symbol of `L` occurs in `S`. -/
@[simp]
theorem mem_functionsInSet_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    {s : Σ k, (symbSublang F R).Functions k} :
    s ∈ functionsInSet (restrictSymbolsSet S hF hR) ↔
      (⟨s.1, s.2.1⟩ : Σ k, L.Functions k) ∈ functionsInSet S := by
  simp only [functionsInSet_def, Set.mem_iUnion, mem_restrictSymbolsSet_iff]
  refine ⟨?_, fun ⟨φ, hφ, hs⟩ => ⟨_, ⟨φ, hφ, rfl⟩, (φ.mem_functionsIn_restrictSymbols _ _).2 hs⟩⟩
  rintro ⟨_, ⟨φ, hφ, rfl⟩, hs⟩
  exact ⟨φ, hφ, (φ.mem_functionsIn_restrictSymbols _ _).1 hs⟩

/-- A relation symbol of `symbSublang F R` occurs in `restrictSymbolsSet S hF hR` iff its
underlying symbol of `L` occurs in `S`. -/
@[simp]
theorem mem_relationsInSet_restrictSymbolsSet (S : Set (L.BoundedFormulaInf ι α n))
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    {s : Σ k, (symbSublang F R).Relations k} :
    s ∈ relationsInSet (restrictSymbolsSet S hF hR) ↔
      (⟨s.1, s.2.1⟩ : Σ k, L.Relations k) ∈ relationsInSet S := by
  simp only [relationsInSet_def, Set.mem_iUnion, mem_restrictSymbolsSet_iff]
  refine ⟨?_, fun ⟨φ, hφ, hs⟩ => ⟨_, ⟨φ, hφ, rfl⟩, (φ.mem_relationsIn_restrictSymbols _ _).2 hs⟩⟩
  rintro ⟨_, ⟨φ, hφ, rfl⟩, hs⟩
  exact ⟨φ, hφ, (φ.mem_relationsIn_restrictSymbols _ _).1 hs⟩

/-- Restricting a countable set of formulas gives a countable set of formulas in the sublanguage. -/
theorem countable_restrictSymbolsSet {S : Set (L.BoundedFormulaInf ι α n)} (hS : S.Countable)
    (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R) :
    (restrictSymbolsSet S hF hR).Countable := by
  have := hS.to_subtype
  exact Set.countable_range _

/-- Along any expansion of `symbSublangIncl F R`, every formula in `restrictSymbolsSet S hF hR` is
realized at `(v, xs)` iff every formula in `S` is. -/
theorem forall_realize_restrictSymbolsSet_iff {M : Type w} [L.Structure M]
    [(symbSublang F R).Structure M] [(symbSublangIncl F R).IsExpansionOn M]
    (S : Set (L.BoundedFormulaInf ι α n)) (hF : functionsInSet S ⊆ F) (hR : relationsInSet S ⊆ R)
    (v : α → M) (xs : Fin n → M) :
    (∀ ψ ∈ restrictSymbolsSet S hF hR, ψ.Realize v xs) ↔ ∀ φ ∈ S, φ.Realize v xs := by
  simp only [restrictSymbolsSet, Set.forall_mem_range, Subtype.forall, realize_restrictSymbols]

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
def toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    Set ((setSymbSublang S).BoundedFormulaInf ι α n) :=
  restrictSymbolsSet S subset_rfl subset_rfl

/-- Unfolding equation for `toSetSymbSublang`. -/
theorem toSetSymbSublang_def (S : Set (L.BoundedFormulaInf ι α n)) :
    toSetSymbSublang S = restrictSymbolsSet S subset_rfl subset_rfl :=
  (rfl)

/-- Translating `toSetSymbSublang S` along `setSymbSublangIncl S` recovers `S`. -/
@[simp]
theorem image_onBoundedFormulaInf_toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    (setSymbSublangIncl S).onBoundedFormulaInf '' toSetSymbSublang S = S :=
  image_onBoundedFormulaInf_restrictSymbolsSet S subset_rfl subset_rfl

/-- `toSetSymbSublang S` is countable whenever `S` is countable. -/
theorem countable_toSetSymbSublang {S : Set (L.BoundedFormulaInf ι α n)} (hS : S.Countable) :
    (toSetSymbSublang S).Countable :=
  countable_restrictSymbolsSet hS subset_rfl subset_rfl

/-- Every function symbol of `setSymbSublang S` occurs in `toSetSymbSublang S`. -/
@[simp]
theorem functionsInSet_toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (toSetSymbSublang S) = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (mem_functionsInSet_restrictSymbolsSet S subset_rfl subset_rfl).2 s.2.2

/-- Every relation symbol of `setSymbSublang S` occurs in `toSetSymbSublang S`. -/
@[simp]
theorem relationsInSet_toSetSymbSublang (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (toSetSymbSublang S) = Set.univ :=
  Set.eq_univ_of_forall fun s =>
    (mem_relationsInSet_restrictSymbolsSet S subset_rfl subset_rfl).2 s.2.2

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
theorem realize_expandSymbStructure_reduct {M : Type w} [L.Structure M] [Nonempty (L.Structure M)]
    (φ : L.SentenceInf ι) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    @SentenceInf.Realize L ι φ M (@expandSymbStructure L F R M _ ((symbSublangIncl F R).reduct M)) ↔
      SentenceInf.Realize φ M := by
  let : (symbSublang F R).Structure M := (symbSublangIncl F R).reduct M
  exact realize_congr_of_isExpansionOn_symbSublangIncl (expandSymbStructure F R M) _ φ hF hR

/-- Along any expansion of `φ.symbSublangIncl`, `φ.toSymbSublang` holds iff `φ` does. -/
@[simp]
theorem realize_toSymbSublang {M : Type w} [L.Structure M] (φ : L.SentenceInf ι)
    [φ.symbSublang.Structure M] [φ.symbSublangIncl.IsExpansionOn M] :
    SentenceInf.Realize φ.toSymbSublang M ↔ SentenceInf.Realize φ M :=
  realize_restrictSymbols φ subset_rfl subset_rfl

/-- Expanding a `φ.symbSublang`-structure on `M` via `expandSymbStructure` satisfies `φ` iff the
`φ.symbSublang`-structure satisfies `φ.toSymbSublang`. -/
theorem realize_expandSymbStructure_toSymbSublang {M : Type w} [Nonempty (L.Structure M)]
    (φ : L.SentenceInf ι) [φ.symbSublang.Structure M] :
    @SentenceInf.Realize L ι φ M (expandSymbStructure φ.functionsIn φ.relationsIn M) ↔
      SentenceInf.Realize φ.toSymbSublang M :=
  realize_expandSymbStructure φ subset_rfl subset_rfl

/-- Along any expansion of `symbSublangIncl F R`, every sentence in
`BoundedFormulaInf.restrictSymbolsSet S hF hR` holds in `M` iff every sentence in `S` does. -/
theorem forall_realize_restrictSymbolsSet_iff {M : Type w} [L.Structure M]
    [(symbSublang F R).Structure M] [(symbSublangIncl F R).IsExpansionOn M]
    (S : Set (L.SentenceInf ι)) (hF : BoundedFormulaInf.functionsInSet S ⊆ F)
    (hR : BoundedFormulaInf.relationsInSet S ⊆ R) :
    (∀ ψ ∈ (BoundedFormulaInf.restrictSymbolsSet S hF hR : Set ((symbSublang F R).SentenceInf ι)),
      SentenceInf.Realize ψ M) ↔ ∀ φ ∈ S, SentenceInf.Realize φ M := by
  simp only [BoundedFormulaInf.restrictSymbolsSet, Set.forall_mem_range, Subtype.forall,
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
  rw [← comp_onBoundedFormulaInf, hh, BoundedFormulaInf.onBoundedFormulaInf_toSymbSublang]

end LHom

end Language

end FirstOrder
