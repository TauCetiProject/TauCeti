/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Symbols
public import TauCeti.ModelTheory.Sublanguage

/-!
# Restricting infinitary formulas to symbol sublanguages

A formula of `L` whose occurring symbols lie in `F` and `R` restricts to the symbol sublanguage
`symbSublang F R` (`BoundedFormulaInf.restrictSymbols`), and translating the restriction back along
the inclusion `symbSublangIncl F R` recovers the formula. At a countable carrier a formula mentions
only countably many symbols (`BoundedFormulaInf.functionsIn_countable`), so the sublanguage of its
own symbols has countably many symbols of each sort, whatever the size of `L`. Truth is unaffected:
the restriction is realized in any structure on which the inclusion is an expansion, for instance in
the reduct of an `L`-structure, or in an `L`-structure expanding a structure of the sublanguage
(Mathlib's `LHom.defaultExpansion` with `symbSublangIncl_injective`), exactly when the formula is.
This is how statements proved for countable languages reach sentences of arbitrary languages.

The restriction also pulls formulas back along an arbitrary language map `g : L →ᴸ L'`: a formula
of `L'` whose occurring symbols all lie in the range of `g` is the image under `g` of a formula of
`L`. No injectivity of `g` is needed, since the inclusion of the sublanguage factors through `g`
(`LHom.exists_comp_eq_symbSublangIncl`).

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.restrictSymbols`: the restriction of an infinitary formula
  to a sublanguage containing its symbols.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.onBoundedFormulaInf_restrictSymbols`: the inclusion sends
  the restriction back to the formula.
* `FirstOrder.Language.BoundedFormulaInf.realize_restrictSymbols`: the restriction is realized
  exactly when the formula is.
* `FirstOrder.Language.LHom.exists_eq_onBoundedFormulaInf_of_subset_range`: a formula whose symbols
  lie in the range of a language map is the image of a formula.

## References

* The restriction of formulas follows `BoundedFormulaω.restrictSymbols` of
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/GeneratedSublanguage.lean`.
  Divergences from that source: the restriction is defined at every carrier `ι` rather than at `ℕ`,
  and the realization of a restriction and the pullback along an arbitrary language map are new.
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
