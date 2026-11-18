/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The long exact sequence of a triple in relative singular cohomology

For a triple `B ⊆ A ⊆ X` of topological spaces, the short exact sequence of relative singular
chain complexes `0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0` splits in every degree because the
quotient `C(X) ⟶ C(X, A)` splits degreewise. Applying the contravariant functor `Hom(-, M)`
therefore produces a short exact sequence of relative singular cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TopTriple.singularCochainComplexShortComplex`,
`TopTriple.shortExact_singularCochainComplexShortComplex`), whose long exact cohomology sequence
is the cohomology sequence of the triple

`⋯ ⟶ Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B) ⟶ Hⁿ⁺¹(X, A) ⟶ ⋯`.

When retractions out of `Hⁿ(X, B)` and `Hⁿ⁺¹(X, B)` split the outer maps `H*(X, A) ⟶ H*(X, B)`
up to isomorphism, the connecting morphism vanishes and `Hⁿ(X, B)` splits as a binary biproduct
(`TopTriple.isIso_biprod_lift_singularCohomology`).

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (T : TopTriple.{w}) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The relative singular cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple
`T = (X, A, B)`. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (totalToOuter.app T))
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (innerToTotal.app T))
    (((T.singularChainComplexShortComplex R).op.map
      (TauCeti.ChainComplex.linearYonedaFunctor k M)).zero)

/-- The cochain sequence of a triple is the image under `Hom(-, M)` of its relative singular
chain sequence. -/
lemma singularCochainComplexShortComplex_eq_map :
    T.singularCochainComplexShortComplex R k M =
      (T.singularChainComplexShortComplex R).op.map
        (TauCeti.ChainComplex.linearYonedaFunctor k M) :=
  (rfl)

/-- The first map of the cochain sequence of a triple is induced by `totalToOuter`. -/
@[simp]
lemma singularCochainComplexShortComplex_f_eq :
    (T.singularCochainComplexShortComplex R k M).f =
      TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (totalToOuter.app T) :=
  (rfl)

/-- The second map of the cochain sequence of a triple is induced by `innerToTotal`. -/
@[simp]
lemma singularCochainComplexShortComplex_g_eq :
    (T.singularCochainComplexShortComplex R k M).g =
      TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (innerToTotal.app T) :=
  (rfl)

/-- The relative singular cochain sequence `0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0` of a triple
is short exact. -/
theorem shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact := by
  have : ∀ i, IsSplitMono ((T.singularChainComplexShortComplex R).f.f i) := fun i ↦ by
    let P := TopPair.toSSetPair.obj (outerPair.obj T)
    have hsec : ((SSetPair.chainComplexXSplitting R P i).s ≫
          ((totalPair.obj T).singularChainComplexπ R).f i) ≫
        (TopPair.singularChainComplexMap (totalToOuter.app T) R).f i = 𝟙 _ :=
      (Category.assoc _ _ _).trans <|
        (congrArg ((SSetPair.chainComplexXSplitting R P i).s ≫ ·)
          ((HomologicalComplex.comp_f _ _ i).symm.trans
            (congrArg (fun φ ↦ φ.f i) (T.singularChainComplexπ_comp_totalToOuter R)))).trans
          (SSetPair.chainComplexXSplitting R P i).s_g
    exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (T.shortExact_singularChainComplexShortComplex R) i).isSplitMono_f_iff_isSplitEpi_g.2
        (IsSplitEpi.mk' ⟨_, hsec⟩)
  rw [singularCochainComplexShortComplex_eq_map]
  exact TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

/-- The maps `Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B)` of a triple compose to zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyMap_totalToOuter_comp_innerToTotal (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n ≫
      TopPair.singularCohomologyMap (innerToTotal.app T) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, (T.singularCochainComplexShortComplex R k M).zero,
    HomologicalComplex.homologyMap_zero]

/-- The connecting morphism `Hⁿ(A, B) ⟶ Hᵐ(X, A)` in the long exact cohomology sequence of a
triple `T = (X, A, B)`, where `n + 1 = m`. -/
abbrev singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (innerPair.obj T).singularCohomology R k M n ⟶
      (outerPair.obj T).singularCohomology R k M m :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularCohomologyδ_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    T.singularCohomologyδ R k M n m h ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) m = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma comp_singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n ≫
      T.singularCohomologyδ R k M n m h = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).comp_δ n m (by simpa)

/-- Exactness at `Hᵐ(X, A)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_outer (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.singularCohomologyδ_comp R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₁ n m (by simpa)

/-- Exactness at `Hⁿ(X, B)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_total (n : ℕ) :
    (ShortComplex.mk _ _
      (T.singularCohomologyMap_totalToOuter_comp_innerToTotal R k M n)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₂ n

/-- Exactness at `Hⁿ(A, B)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_inner (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.comp_singularCohomologyδ R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₃ n m (by simpa)

/-- **Splitting the cohomology sequence of a triple.** In a triple `T = (X, A, B)`, if morphisms
out of `Hⁿ(X, B)` and `Hⁿ⁺¹(X, B)` compose with `H*(X, A) ⟶ H*(X, B)` to isomorphisms, then
`Hⁿ(X, B) ⟶ B₀ ⊞ Hⁿ(A, B)` is an isomorphism. -/
theorem isIso_biprod_lift_singularCohomology (n : ℕ) {B₀ B₁ : ModuleCat.{v} k}
    (p₀ : (totalPair.obj T).singularCohomology R k M n ⟶ B₀)
    (p₁ : (totalPair.obj T).singularCohomology R k M (n + 1) ⟶ B₁)
    (hp₀ : IsIso (TopPair.singularCohomologyMap (totalToOuter.app T) n ≫ p₀))
    (hp₁ : IsIso (TopPair.singularCohomologyMap (totalToOuter.app T) (n + 1) ≫ p₁)) :
    IsIso (biprod.lift p₀ (TopPair.singularCohomologyMap (innerToTotal.app T) n)) := by
  let q₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n
  let q₁ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) (n + 1)
  let i₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n
  have hδ : T.singularCohomologyδ R k M n (n + 1) rfl = 0 := by
    rw [← Category.comp_id (T.singularCohomologyδ R k M n (n + 1) rfl),
      ← IsIso.hom_inv_id (q₁ ≫ p₁), ← Category.assoc, ← Category.assoc,
      T.singularCohomologyδ_comp R k M n (n + 1) rfl, zero_comp, zero_comp]
  have hepi : Epi i₀ := (T.singularCohomology_exact_inner R k M n (n + 1) rfl).epi_f hδ
  let r' : (totalPair.obj T).singularCohomology R k M n ⟶
      (outerPair.obj T).singularCohomology R k M n := p₀ ≫ inv (q₀ ≫ p₀)
  have hr' : q₀ ≫ r' = 𝟙 _ := by
    dsimp only [r']
    rw [← Category.assoc]
    exact IsIso.hom_inv_id _
  let spl := ShortComplex.Splitting.ofExactOfRetraction _
    (T.singularCohomology_exact_total R k M n) r' hr' hepi
  have hspl : IsIso (biprod.lift r' i₀) := spl.isoBinaryBiproduct.isIso_hom
  have hfac : biprod.lift r' i₀ ≫ (biprod.mapIso (asIso (q₀ ≫ p₀)) (Iso.refl _)).hom =
      biprod.lift p₀ i₀ :=
    biprod.hom_ext _ _ (by simp [r', biprod.lift_fst_assoc]) (by simp)
  rw [← hfac]
  infer_instance

end TopTriple

end TauCeti
