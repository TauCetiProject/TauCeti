/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# The Mayer–Vietoris sequence in singular cohomology

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`, let `R` and `M` be
objects of a `k`-linear abelian category with coproducts, and write `Hⁿ(-)` for singular
cohomology `Hⁿ(-; R, M)`, the cohomology of `Hom(C(-; R), M)`. This file constructs the
Mayer–Vietoris long exact sequence
`⋯ ⟶ Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V) ⟶ Hⁿ⁺¹(X) ⟶ ⋯`,
whose first map is `(j_U^*, j_V^*)` and whose second map is `i_U^* - i_V^*`, the `i` and `j`
being the inclusions. These are the maps dual to the maps `j_U + j_V` and `(i_U, -i_V)` of the
Mayer–Vietoris sequence in singular homology. The connecting morphism is natural in maps of
covered spaces.

The construction dualizes the one in homology. For a pushout square of simplicial sets
```
     t
 X₁  ⟶  X₂
l|       |r
 v       v
 X₃  ⟶  X₄
     b
```
whose top map is a monomorphism, the Mayer–Vietoris short exact sequence of chain complexes is
split in each degree, so applying `Hom(-, M)` keeps it short exact
(`SSet.shortExact_mayerVietorisCochainShortComplex`). Its cohomology sequence is a long exact
sequence `⋯ ⟶ Hⁿ(X₄) ⟶ Hⁿ(X₂) ⊞ Hⁿ(X₃) ⟶ Hⁿ(X₁) ⟶ Hⁿ⁺¹(X₄) ⟶ ⋯`, natural in maps of pushout
squares. For the singular simplicial sets of `U ∩ V`, `U`, `V` and the subcomplex of singular
simplices of `X` lying in `U` or in `V`, the small-chain theorem identifies the cohomology of that
subcomplex with the singular cohomology of `X` (`TauCeti.smallSingularCohomologyIso`).

## Main definitions and results

* `SSet.shortExact_mayerVietorisCochainShortComplex`: the cochain Mayer–Vietoris sequence of a
  pushout square of simplicial sets is short exact.
* `SSet.mayerVietorisCochainToBiprod`, `SSet.mayerVietorisCochainFromBiprod` and
  `SSet.mayerVietorisCochainδ`: the maps of its long exact cohomology sequence, exact by
  `SSet.mayerVietorisCochain_exact₁`, `SSet.mayerVietorisCochain_exact₂` and
  `SSet.mayerVietorisCochain_exact₃`, with connecting morphism natural in maps of pushout squares
  (`SSet.mayerVietorisCochainδ_naturality`).
* `TauCeti.smallSingularCohomologyIso`: restricting cochains to the chains subordinate to an open
  cover is an isomorphism on cohomology, natural in maps of covered spaces
  (`TauCeti.smallSingularCohomologyIso_naturality`).
* `TopCat.singularCohomologyMayerVietorisToBiprod` and
  `TopCat.singularCohomologyMayerVietorisFromBiprod`: the maps `Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` and
  `Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V)`.
* `TopCat.singularCohomologyMayerVietorisδ`: the connecting morphism `Hⁿ(U ∩ V) ⟶ Hᵐ(X)`,
  `n + 1 = m`, characterized by `TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap`.
* `TopCat.singularCohomologyMayerVietoris_exact₁`, `TopCat.singularCohomologyMayerVietoris_exact₂`,
  `TopCat.singularCohomologyMayerVietoris_exact₃`: exactness at `Hᵐ(X)`, at `Hⁿ(U) ⊞ Hⁿ(V)` and at
  `Hⁿ(U ∩ V)`.
* `TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero`: injectivity at the degree-zero
  endpoint.
* `TopCat.singularCohomologyMayerVietorisδ_naturality`: naturality of the connecting morphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the Mayer–Vietoris sequences in cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- The cochain Mayer–Vietoris sequence `Hom(C(X₄), M) ⟶ Hom(C(X₂), M) ⊞ Hom(C(X₃), M) ⟶
Hom(C(X₁), M)` of a commutative square of simplicial sets, with first map `(r^*, b^*)` and second
map `t^* - l^*`. It is the image under `Hom(-, M)` of the chain Mayer–Vietoris sequence, once
`Hom(C(X₂) ⊞ C(X₃), M)` is identified with `Hom(C(X₂), M) ⊞ Hom(C(X₃), M)`. -/
abbrev mayerVietorisCochainShortComplex (sq : CommSq t l r b) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (biprod.lift (cochainComplexMap (R := R) (k := k) (M := M) r) (cochainComplexMap b))
    (biprod.desc (cochainComplexMap t) (-cochainComplexMap l))
    (by simp [← cochainComplexMap_comp, sq.w])

/-- **The cochain Mayer–Vietoris short exact sequence.** For a pushout square of simplicial sets
whose top map is a monomorphism, the cochain Mayer–Vietoris sequence is short exact. -/
lemma shortExact_mayerVietorisCochainShortComplex (sq : IsPushout t l r b) [Mono t] :
    (mayerVietorisCochainShortComplex R k M sq.toCommSq).ShortExact := by
  -- Unfold `cochainComplexMap`, so that the terms of the sequence are written as
  -- `(linearYonedaFunctor k M).obj`, the form in which `Hom(-, M)` is applied to the chain
  -- Mayer–Vietoris sequence below.
  change (ShortComplex.mk
    (biprod.lift ((linearYonedaFunctor k M).map (chainComplexMap r R).op)
      ((linearYonedaFunctor k M).map (chainComplexMap b R).op))
    (biprod.desc ((linearYonedaFunctor k M).map (chainComplexMap t R).op)
      (-(linearYonedaFunctor k M).map (chainComplexMap l R).op)) _).ShortExact
  let S : ShortComplex (ChainComplex C ℕ) :=
    ShortComplex.mk (biprod.lift (chainComplexMap t R) (-chainComplexMap l R))
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R))
      (by simp [← Functor.map_comp, sq.w])
  have hS : S.ShortExact := shortExact_mayerVietorisShortComplex R sq
  -- `SSetPair.of t` has `t` as its structure map, so this is the split monomorphism instance for
  -- the chains of a pair of simplicial sets.
  have ht (i : ℕ) : IsSplitMono ((chainComplexMap t R).f i) :=
    inferInstanceAs (IsSplitMono ((chainComplexMap (SSetPair.of t).hom R).f i))
  have (i : ℕ) : IsSplitMono (S.f.f i) :=
    IsSplitMono.mk'
      { retraction := (biprod.fst : X₂.chainComplex R ⊞ X₃.chainComplex R ⟶ _).f i ≫
          @retraction _ _ _ _ ((chainComplexMap t R).f i) (ht i)
        id := by rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_fst,
          IsSplitMono.id] }
  have he : ((linearYonedaFunctor k M).mapIso (biprod.opIso _ _) ≪≫
      (linearYonedaFunctor k M).mapBiprod _ _).inv =
        biprod.desc ((linearYonedaFunctor k M).map
          (biprod.fst : X₂.chainComplex R ⊞ X₃.chainComplex R ⟶ _).op)
          ((linearYonedaFunctor k M).map biprod.snd.op) := by
    rw [Iso.trans_inv, Functor.mapIso_inv, Functor.mapBiprod_inv]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, ← Functor.map_comp, biprod.inl_opIso_inv, biprod.inl_desc]
    · rw [biprod.inr_desc_assoc, ← Functor.map_comp, biprod.inr_opIso_inv, biprod.inr_desc]
  -- `Hom(-, M)` keeps the degreewise split chain sequence short exact; it remains to identify
  -- `Hom(C(X₂) ⊞ C(X₃), M)` with `Hom(C(X₂), M) ⊞ Hom(C(X₃), M)` compatibly with the maps.
  refine ShortComplex.shortExact_of_iso (Iso.symm ?_) (shortExact_map_linearYonedaFunctor k M hS)
  refine ShortComplex.isoMk (Iso.refl ((linearYonedaFunctor k M).obj (op (X₄.chainComplex R))))
    (((linearYonedaFunctor k M).mapIso (biprod.opIso _ _) ≪≫
      (linearYonedaFunctor k M).mapBiprod _ _).symm)
    (Iso.refl ((linearYonedaFunctor k M).obj (op (X₁.chainComplex R)))) ?_ ?_
  · rw [Iso.symm_hom, he]
    dsimp [S, ShortComplex.op, -linearYonedaFunctor_obj]
    simp [biprod.desc_eq, ← Functor.map_comp, ← op_comp, -linearYonedaFunctor_obj]
  · rw [Iso.symm_hom, he]
    dsimp [S, ShortComplex.op, -linearYonedaFunctor_obj]
    apply biprod.hom_ext' <;>
      simp [← Functor.map_comp, ← op_comp, -linearYonedaFunctor_obj]

/-! ### The long exact sequence of a pushout square -/

/-- The first map `Hⁿ(X₄) ⟶ Hⁿ(X₂) ⊞ Hⁿ(X₃)` of the cochain Mayer–Vietoris sequence, with
components `r^*` and `b^*`. -/
def mayerVietorisCochainToBiprod (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    ((X₄.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((X₂.chainComplex R).linearYonedaObj k M).homology n ⊞
        ((X₃.chainComplex R).linearYonedaObj k M).homology n :=
  biprod.lift (HomologicalComplex.homologyMap (cochainComplexMap r) n)
    (HomologicalComplex.homologyMap (cochainComplexMap b) n)

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_fst (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ biprod.fst =
      HomologicalComplex.homologyMap (cochainComplexMap r) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_snd (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ biprod.snd =
      HomologicalComplex.homologyMap (cochainComplexMap b) n :=
  biprod.lift_snd _ _

/-- The second map `Hⁿ(X₂) ⊞ Hⁿ(X₃) ⟶ Hⁿ(X₁)` of the cochain Mayer–Vietoris sequence, the
difference `t^* - l^*`. -/
def mayerVietorisCochainFromBiprod (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    ((X₂.chainComplex R).linearYonedaObj k M).homology n ⊞
        ((X₃.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((X₁.chainComplex R).linearYonedaObj k M).homology n :=
  biprod.desc (HomologicalComplex.homologyMap (cochainComplexMap t) n)
    (-HomologicalComplex.homologyMap (cochainComplexMap l) n)

@[reassoc (attr := simp)]
lemma inl_mayerVietorisCochainFromBiprod (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    biprod.inl ≫ mayerVietorisCochainFromBiprod R k M t l n =
      HomologicalComplex.homologyMap (cochainComplexMap t) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_mayerVietorisCochainFromBiprod (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    biprod.inr ≫ mayerVietorisCochainFromBiprod R k M t l n =
      -HomologicalComplex.homologyMap (cochainComplexMap l) n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainToBiprod_fromBiprod (sq : CommSq t l r b) (n : ℕ) :
    mayerVietorisCochainToBiprod R k M r b n ≫ mayerVietorisCochainFromBiprod R k M t l n = 0 := by
  simp [mayerVietorisCochainToBiprod, mayerVietorisCochainFromBiprod,
    ← HomologicalComplex.homologyMap_comp, ← cochainComplexMap_comp, sq.w]

private lemma mayerVietorisCochainFromBiprod_eq (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    mayerVietorisCochainFromBiprod R k M t l n =
      biprod.desc (HomologicalComplex.homologyMap (cochainComplexMap t) n)
        (HomologicalComplex.homologyMap (-cochainComplexMap l) n) := by
  rw [mayerVietorisCochainFromBiprod, HomologicalComplex.homologyMap_neg]

variable (sq : IsPushout t l r b) [Mono t]

/-- The cochain Mayer–Vietoris connecting morphism `Hⁿ(X₁) ⟶ Hᵐ(X₄)`, where `n + 1 = m`: the
connecting morphism of the cochain Mayer–Vietoris short exact sequence. -/
def mayerVietorisCochainδ (n m : ℕ) (h : n + 1 = m := by lia) :
    ((X₁.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((X₄.chainComplex R).linearYonedaObj k M).homology m :=
  (shortExact_mayerVietorisCochainShortComplex R k M sq).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma mayerVietorisCochainδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sq n m h ≫ mayerVietorisCochainToBiprod R k M r b m = 0 :=
  (shortExact_mayerVietorisCochainShortComplex R k M sq).δ_comp_biprod_lift_homologyMap n m _

@[reassoc (attr := simp)]
lemma mayerVietorisCochainFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainFromBiprod R k M t l n ≫ mayerVietorisCochainδ R k M sq n m h = 0 := by
  rw [mayerVietorisCochainFromBiprod_eq]
  exact (shortExact_mayerVietorisCochainShortComplex R k M sq).biprod_desc_homologyMap_comp_δ n m _

/-- **Exactness of the cochain Mayer–Vietoris sequence at `Hᵐ(X₄)`.** -/
lemma mayerVietorisCochain_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisCochainδ_toBiprod R k M sq n m h)).Exact :=
  (shortExact_mayerVietorisCochainShortComplex R k M sq).biprod_homology_exact₁ n m _

/-- **Exactness of the cochain Mayer–Vietoris sequence at `Hⁿ(X₂) ⊞ Hⁿ(X₃)`.** -/
lemma mayerVietorisCochain_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisCochainToBiprod_fromBiprod R k M sq.toCommSq n)).Exact := by
  convert (shortExact_mayerVietorisCochainShortComplex R k M sq).biprod_homology_exact₂ n using 2
  exacts [rfl, mayerVietorisCochainFromBiprod_eq R k M t l n]

/-- **Exactness of the cochain Mayer–Vietoris sequence at `Hⁿ(X₁)`.** -/
lemma mayerVietorisCochain_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisCochainFromBiprod_δ R k M sq n m h)).Exact := by
  convert (shortExact_mayerVietorisCochainShortComplex R k M sq).biprod_homology_exact₃ n m
    (by simpa) using 2
  exacts [mayerVietorisCochainFromBiprod_eq R k M t l n, rfl]

include sq in
/-- The map `H⁰(X₄) ⟶ H⁰(X₂) ⊞ H⁰(X₃)` at the start of the cochain Mayer–Vietoris sequence is a
monomorphism. -/
lemma mono_mayerVietorisCochainToBiprod_zero : Mono (mayerVietorisCochainToBiprod R k M r b 0) := by
  have := (shortExact_mayerVietorisCochainShortComplex R k M sq).mono_f
  have : Mono (HomologicalComplex.homologyMap
      (mayerVietorisCochainShortComplex R k M sq.toCommSq).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 fun i h ↦ by
      rw [ComplexShape.up_Rel] at h
      omega
  exact HomologicalComplex.mono_biprod_lift_homologyMap 0

variable {Y₁ Y₂ Y₃ Y₄ : SSet.{w}} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
  (φ₁ : X₁ ⟶ Y₁) (φ₂ : X₂ ⟶ Y₂) (φ₃ : X₃ ⟶ Y₃) (φ₄ : X₄ ⟶ Y₄)

/-- **Naturality of the cochain Mayer–Vietoris connecting morphism** in maps of pushout
squares. -/
@[reassoc]
lemma mayerVietorisCochainδ_naturality (sq' : IsPushout t' l' r' b') [Mono t']
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sq' n m h ≫
        HomologicalComplex.homologyMap (cochainComplexMap φ₄) m =
      HomologicalComplex.homologyMap (cochainComplexMap φ₁) n ≫
        mayerVietorisCochainδ R k M sq n m h := by
  let ψ : mayerVietorisCochainShortComplex R k M sq'.toCommSq ⟶
      mayerVietorisCochainShortComplex R k M sq.toCommSq :=
    { τ₁ := cochainComplexMap φ₄
      τ₂ := biprod.map (cochainComplexMap φ₂) (cochainComplexMap φ₃)
      τ₃ := cochainComplexMap φ₁
      comm₁₂ := by apply biprod.hom_ext <;> simp [← cochainComplexMap_comp, hr, hb]
      comm₂₃ := by apply biprod.hom_ext' <;> simp [← cochainComplexMap_comp, ht, hl] }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m (by simpa)

end SSet

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hcov : ⋃ i, U i = Set.univ)

/-- The isomorphism on singular cohomology induced by restricting cochains to the chains
subordinate to an open cover. It is dual to `TauCeti.smallSingularHomologyIso`. -/
def smallSingularCohomologyIso (n : ℕ) :
    X.singularCohomology R k M n ≅
      (((X.smallSingularSubcomplex U : SSet).chainComplex R).linearYonedaObj k M).homology n :=
  ((smallSingularChainHomotopyEquiv R U hU hcov).linearYonedaFunctorMap k M).toHomologyIso n

/-- The small-chain cohomology isomorphism is the map induced by the inclusion of the singular
simplices subordinate to the cover. -/
@[simp]
lemma smallSingularCohomologyIso_hom (n : ℕ) :
    (smallSingularCohomologyIso R k M U hU hcov n).hom =
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (X.smallSingularSubcomplex U).ι)
        n := by
  simp [smallSingularCohomologyIso, HomotopyEquiv.toHomologyIso, SSet.cochainComplexMap]

/-- The small-chain cohomology isomorphism is natural under maps carrying members of one cover
into members of another. -/
lemma smallSingularCohomologyIso_naturality {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (hV : ∀ j, IsOpen (V j))
    (hcovV : ⋃ j, V j = Set.univ) (n : ℕ) :
    TopCat.singularCohomologyMap f n ≫ (smallSingularCohomologyIso R k M U hU hcov n).hom =
      (smallSingularCohomologyIso R k M V hV hcovV n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (X.smallSingularSubcomplexMap U V f r hf)) n := by
  simp only [smallSingularCohomologyIso_hom, TopCat.singularCohomologyMap,
    TopCat.singularCochainComplexMap, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, TopCat.smallSingularSubcomplexMap_ι]

end TauCeti

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

section Maps

variable (U V : Set X)

/-- The first map `Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` of the Mayer–Vietoris sequence in singular cohomology,
with components the restrictions `j_U^*` and `j_V^*` along the inclusions. -/
def singularCohomologyMayerVietorisToBiprod (n : ℕ) :
    X.singularCohomology R k M n ⟶
      (of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n :=
  biprod.lift (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n)
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n)

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_fst (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.fst =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_snd (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.snd =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n :=
  biprod.lift_snd _ _

/-- The second map `Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V)` of the Mayer–Vietoris sequence in singular
cohomology, the difference `i_U^* - i_V^*` of the restrictions along the inclusions of `U ∩ V`.
It is dual to the map `(i_U, -i_V)` of the homology sequence. -/
def singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    (of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n ⟶
      (of ↥(U ∩ V)).singularCohomology R k M n :=
  biprod.desc
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) n)
    (-TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) n)

@[reassoc (attr := simp)]
lemma inl_singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ singularCohomologyMayerVietorisFromBiprod R k M U V n =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ singularCohomologyMayerVietorisFromBiprod R k M U V n =
      -TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫
      singularCohomologyMayerVietorisFromBiprod R k M U V n = 0 := by
  simp [singularCohomologyMayerVietorisToBiprod, singularCohomologyMayerVietorisFromBiprod,
    ← singularCohomologyMap_comp, (commSq_ofHom_inter U V).w]

end Maps

/-! ### The long exact sequence of an open cover by two sets -/

section Sequence

variable {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The restriction of cochains to the simplices lying in `U` or in `V`, on cohomology. -/
private abbrev smallIso (n : ℕ) :
    X.singularCohomology R k M n ≅
      (((X.smallSingularSubcomplex ![U, V] : SSet).chainComplex R).linearYonedaObj k M).homology
        n :=
  TauCeti.smallSingularCohomologyIso R k M ![U, V] (isOpen_vecCons hU hV) (iUnion_vecCons hUV) n

private lemma smallIso_hom (n : ℕ) :
    (smallIso R k M hU hV hUV n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (X.smallSingularSubcomplex ![U, V]).ι) n :=
  TauCeti.smallSingularCohomologyIso_hom ..

private lemma smallIso_hom_comp_mayerVietorisCochainToBiprod (n : ℕ) :
    (smallIso R k M hU hV hUV n).hom ≫
        SSet.mayerVietorisCochainToBiprod R k M
          (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
          (toSmallSingularSubcomplex ![U, V]
            ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) n =
      singularCohomologyMayerVietorisToBiprod R k M U V n := by
  rw [smallIso_hom]
  apply biprod.hom_ext <;>
    simp [← HomologicalComplex.homologyMap_comp, ← SSet.cochainComplexMap_comp,
      toSmallSingularSubcomplex_ι]

/-- The second map of the cochain Mayer–Vietoris sequence of the singular simplicial sets is the
second map of the Mayer–Vietoris sequence in singular cohomology. -/
private lemma mayerVietorisCochainFromBiprod_eq (n : ℕ) :
    SSet.mayerVietorisCochainFromBiprod R k M
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))) n =
      singularCohomologyMayerVietorisFromBiprod R k M U V n := by
  apply biprod.hom_ext' <;> simp

/-- The Mayer–Vietoris connecting morphism `Hⁿ(U ∩ V) ⟶ Hᵐ(X)` in singular cohomology, where
`n + 1 = m`, for an open cover of `X` by `U` and `V`. It is the connecting morphism of the cochain
Mayer–Vietoris sequence of the singular simplices lying in `U`, in `V` and in `U` or `V`, followed
by the inverse of the restriction isomorphism from the cohomology of `X`. -/
def singularCohomologyMayerVietorisδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (of ↥(U ∩ V)).singularCohomology R k M n ⟶ X.singularCohomology R k M m :=
  SSet.mayerVietorisCochainδ R k M (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h ≫
    (smallIso R k M hU hV hUV m).inv

/-- Followed by restriction to the singular simplices lying in `U` or in `V`, the Mayer–Vietoris
connecting morphism is the connecting morphism of the cochain Mayer–Vietoris sequence of those
simplices. Since that restriction is an isomorphism on cohomology, this characterizes it. -/
@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisδ_comp_homologyMap (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU hV hUV n m h ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (X.smallSingularSubcomplex ![U, V]).ι) m =
      SSet.mayerVietorisCochainδ R k M (isPushout_toSSet_inter_smallSingularSubcomplex U V)
        n m h := by
  rw [singularCohomologyMayerVietorisδ, Category.assoc,
    ← smallIso_hom R k M hU hV hUV, Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU hV hUV n m h ≫
      singularCohomologyMayerVietorisToBiprod R k M U V m = 0 := by
  rw [← smallIso_hom_comp_mayerVietorisCochainToBiprod R k M hU hV hUV,
    singularCohomologyMayerVietorisδ, Category.assoc, Iso.inv_hom_id_assoc,
    SSet.mayerVietorisCochainδ_toBiprod R k M _ n m h]

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisFromBiprod R k M U V n ≫
      singularCohomologyMayerVietorisδ R k M hU hV hUV n m h = 0 := by
  rw [← mayerVietorisCochainFromBiprod_eq, singularCohomologyMayerVietorisδ,
    SSet.mayerVietorisCochainFromBiprod_δ_assoc R k M _ n m h, zero_comp]

/-- **Exactness of the Mayer–Vietoris sequence at `Hᵐ(X)`.** -/
lemma singularCohomologyMayerVietoris_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisδ_toBiprod R k M hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietorisCochain_exact₁ R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (smallIso R k M hU hV hUV m).symm (Iso.refl _) ?_ ?_
  · simp [singularCohomologyMayerVietorisδ]
  · dsimp only
    rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← smallIso_hom_comp_mayerVietorisCochainToBiprod R k M hU hV hUV, Iso.inv_hom_id_assoc]

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U) ⊞ Hⁿ(V)`.** -/
lemma singularCohomologyMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisToBiprod_fromBiprod R k M U V n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietorisCochain_exact₂ R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V) n)
  refine ShortComplex.isoMk (smallIso R k M hU hV hUV n).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp only
    rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← smallIso_hom_comp_mayerVietorisCochainToBiprod R k M hU hV hUV, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id,
      mayerVietorisCochainFromBiprod_eq]

/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U ∩ V)`.** -/
lemma singularCohomologyMayerVietoris_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisFromBiprod_δ R k M hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietorisCochain_exact₃ R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (smallIso R k M hU hV hUV m).symm ?_ ?_
  · dsimp only
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id,
      mayerVietorisCochainFromBiprod_eq]
  · simp [singularCohomologyMayerVietorisδ]

include hU hV hUV in
/-- The map `H⁰(X) ⟶ H⁰(U) ⊞ H⁰(V)` at the start of the Mayer–Vietoris sequence is a
monomorphism. -/
lemma mono_singularCohomologyMayerVietorisToBiprod_zero :
    Mono (singularCohomologyMayerVietorisToBiprod R k M U V 0) := by
  have := SSet.mono_mayerVietorisCochainToBiprod_zero R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
  rw [← smallIso_hom_comp_mayerVietorisCochainToBiprod R k M hU hV hUV]
  infer_instance

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V')
  (hUV' : U' ∪ V' = Set.univ) (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- **Naturality of the Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying `U` into
`U'` and `V` into `V'` commutes with the connecting morphisms, where `U ∩ V ⟶ U' ∩ V'` is the
restriction of `f`. -/
@[reassoc]
lemma singularCohomologyMayerVietorisδ_naturality (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU' hV' hUV' n m h ≫ TopCat.singularCohomologyMap f m =
      TopCat.singularCohomologyMap (ofHom ⟨(hfU.inter_inter hfV).restrict,
          f.hom.continuous.restrict (hfU.inter_inter hfV)⟩) n ≫
        singularCohomologyMayerVietorisδ R k M hU hV hUV n m h := by
  have hf : ∀ i, Set.MapsTo f (![U, V] i) (![U', V'] (id i)) := by
    simp [Fin.forall_fin_two, hfU, hfV]
  have hsmall : (smallIso R k M hU' hV' hUV' m).inv ≫ TopCat.singularCohomologyMap f m =
      HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id hf)) m ≫
        (smallIso R k M hU hV hUV m).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact TauCeti.smallSingularCohomologyIso_naturality R k M ![U, V] (isOpen_vecCons hU hV)
      (iUnion_vecCons hUV) ![U', V'] f id hf (isOpen_vecCons hU' hV') (iUnion_vecCons hUV') m
  have hnat := SSet.mayerVietorisCochainδ_naturality R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (toSSet.map (ofHom ⟨(hfU.inter_inter hfV).restrict,
      f.hom.continuous.restrict (hfU.inter_inter hfV)⟩))
    (toSSet.map (ofHom ⟨hfU.restrict, f.hom.continuous.restrict hfU⟩))
    (toSSet.map (ofHom ⟨hfV.restrict, f.hom.continuous.restrict hfV⟩))
    (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id hf)
    (isPushout_toSSet_inter_smallSingularSubcomplex U' V')
    (by rw [← Functor.map_comp, ← Functor.map_comp, ofHom_inclusion_comp])
    (by rw [← Functor.map_comp, ← Functor.map_comp, ofHom_inclusion_comp])
    (toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id hf _ _ hfU)
    (toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id hf _ _ hfV) n m h
  rw [singularCohomologyMayerVietorisδ, singularCohomologyMayerVietorisδ, Category.assoc, hsmall,
    ← Category.assoc, hnat, Category.assoc]

end Sequence

end TopCat
