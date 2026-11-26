/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.RingHomProperties
public import TauCeti.AlgebraicGeometry.Sites.Fppf.MorphismProperty
public import TauCeti.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize

/-!
# Morphism properties local in the étale topology

A property `P` of morphisms of schemes is *étale-local on source and target* (Stacks,
Definition 35.32.3 (04QZ)) when it is local at the source and at the target for
`Scheme.etalePrecoverage` and respects postcomposition with open immersions
(`[P.RespectsRight @IsOpenImmersion]`). Such a property respects composition with arbitrary étale
morphisms on both sides and is invariant under commutative squares whose vertical maps are étale
and surjective on the source (Stacks, Lemma 35.32.6 (04R2)).

This invariance is what makes étale-local properties of morphisms of algebraic spaces independent
of the choice of étale charts.

General precoverage locality lemmas (`respectsLeft_of_isLocalAtSource_precoverage`,
`isStableUnderBaseChangeAgainst_of_isLocalAtTarget_precoverage`,
`of_isEmpty_of_isLocalAtSource_precoverage`, `of_isPullback_pair_of_isLocalAtSource_precoverage`),
Zariski open-immersion stability instances (`IsZariskiLocalAtSource.respectsRight_isOpenImmersion`,
`HasRingHomProperty.respectsRight_isOpenImmersion`), and fppf descent-to-locality instances live in
`TauCeti.AlgebraicGeometry.Sites.MorphismProperty`,
`TauCeti.AlgebraicGeometry.Morphisms.Basic`,
`TauCeti.AlgebraicGeometry.Morphisms.RingHomProperties`,
`TauCeti.AlgebraicGeometry.Sites.Descent`, and
`TauCeti.AlgebraicGeometry.Sites.Fppf.MorphismProperty`.

## Main results

* `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_etalePrecoverage` and
  `AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage`: inclusions between the Zariski,
  étale, and fppf precoverages.
* `CategoryTheory.MorphismProperty.isLocalAtTarget_etalePrecoverage_of_fppfPrecoverage`: target
  locality for `Scheme.fppfPrecoverage` implies target locality for `Scheme.etalePrecoverage`.
* `CategoryTheory.MorphismProperty.respectsLeft_etale_of_isLocalAtSource` and
  `CategoryTheory.MorphismProperty.isStableUnderBaseChangeAgainst_etale_of_isLocalAtTarget`:
  étale specializations of the general precoverage stability theorems.
* `CategoryTheory.MorphismProperty.respectsRight_etale_of_isLocal` and
  `CategoryTheory.MorphismProperty.respects_etale_of_isLocal`: if `P` is Zariski-local at the
  source, étale-local at the target, and respects postcomposition with open immersions, then `P`
  respects postcomposition (and under étale source locality, two-sided composition) with étale
  morphisms (Stacks, Lemma 35.32.6 (04R2)).
* `CategoryTheory.MorphismProperty.of_etale_commSq`,
  `CategoryTheory.MorphismProperty.of_etale_surjective_commSq`, and
  `CategoryTheory.MorphismProperty.iff_of_etale_surjective_commSq`: invariance of `P` on
  commutative squares with étale vertical morphisms.

## Implementation notes

The non-trivial half of Stacks, Lemma 35.32.6 (04R2) is stability under postcomposition with an
étale morphism `e : V ⟶ Y`. Precomposition and base change along a non-surjective étale morphism
`e : U' ⟶ U` follow from the general precoverage results in
`TauCeti.AlgebraicGeometry.Sites.MorphismProperty` by adjoining `𝟙 U` to obtain the two-arrow
covering `{e, 𝟙 U}`. For postcomposition with an étale `e`, Zariski localization using
`Algebra.IsEtaleAt.exists_isStandardEtale` reduces to a standard étale morphism, which is separated
and has bounded geometric fibres. Induction on the fibre bound then factors `e` through its open
image `O ⊆ Y`, pulls back along the étale covering `e' : V ⟶ O`, and splits `V ×_O V` into the
clopen diagonal `Δ(V)` and its open complement, on which the fibre bound drops by one.

## References

* [Stacks Project, Definition 35.32.3](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Lemma 35.32.6](https://stacks.math.columbia.edu/tag/04R2)
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

/-- Every Zariski covering of a scheme is an étale covering. -/
theorem AlgebraicGeometry.Scheme.zariskiPrecoverage_le_etalePrecoverage :
    Scheme.zariskiPrecoverage.{u} ≤ Scheme.etalePrecoverage.{u} :=
  Scheme.precoverage_mono (P := @IsOpenImmersion) (Q := @Etale) fun _ _ _ _ ↦ inferInstance

/-- Every étale covering of a scheme is an fppf covering. -/
theorem AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage :
    Scheme.etalePrecoverage.{u} ≤ Scheme.fppfPrecoverage.{u} :=
  Scheme.precoverage_mono (P := @Etale) (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

/-- Étale morphisms of schemes respect composition with étale morphisms on both sides. -/
instance AlgebraicGeometry.Etale.respects_etale :
    MorphismProperty.Respects @Etale.{u} @Etale.{u} where
  precomp _ _ _ _ := inferInstance
  postcomp _ _ _ _ := inferInstance

namespace CategoryTheory.MorphismProperty

/-- A property of scheme morphisms local at the source for the étale precoverage is Zariski-local
at the source. -/
theorem isZariskiLocalAtSource_of_etalePrecoverage (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] : IsZariskiLocalAtSource P :=
  IsLocalAtSource.of_le Scheme.zariskiPrecoverage_le_etalePrecoverage

/-- A property of scheme morphisms local at the target for the étale precoverage is Zariski-local
at the target. -/
theorem isZariskiLocalAtTarget_of_etalePrecoverage (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.etalePrecoverage] : IsZariskiLocalAtTarget P :=
  IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_etalePrecoverage

/-- Any scheme morphism property local at the target for `Scheme.fppfPrecoverage` is local at the
target for `Scheme.etalePrecoverage`. -/
instance isLocalAtTarget_etalePrecoverage_of_fppfPrecoverage
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] :
    P.IsLocalAtTarget Scheme.etalePrecoverage :=
  IsLocalAtTarget.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-- Specializes `isLocalAtTarget_etalePrecoverage_of_fppfPrecoverage` to raw scheme morphism
predicates at `instances` transparency. -/
instance isLocalAtTarget_etalePrecoverage_of_fppfPrecoverage'
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    [IsLocalAtTarget P Scheme.fppfPrecoverage] :
    IsLocalAtTarget P Scheme.etalePrecoverage :=
  IsLocalAtTarget.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-- If `P` is local at the source for `Scheme.etalePrecoverage`, then `P` respects precomposition
with étale morphisms. -/
instance respectsLeft_etale_of_isLocalAtSource (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] : P.RespectsLeft @Etale :=
  have : MorphismProperty.ContainsIdentities @Etale.{u} :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : P.IsLocalAtSource (Scheme.precoverage @Etale) := ‹_›
  respectsLeft_of_isLocalAtSource_precoverage P @Etale

/-- Specializes `respectsLeft_etale_of_isLocalAtSource` to raw scheme morphism predicates at
`instances` transparency. -/
instance respectsLeft_etale_of_isLocalAtSource' (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    [IsLocalAtSource P Scheme.etalePrecoverage] : RespectsLeft P @Etale :=
  let P' : MorphismProperty Scheme.{u} := P
  have : P'.IsLocalAtSource Scheme.etalePrecoverage := ‹_›
  respectsLeft_etale_of_isLocalAtSource P'

/-- If `P` is local at the target for `Scheme.etalePrecoverage`, then `P` is stable under base
change along étale morphisms. -/
instance isStableUnderBaseChangeAgainst_etale_of_isLocalAtTarget (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.etalePrecoverage] : P.IsStableUnderBaseChangeAgainst @Etale :=
  have : MorphismProperty.ContainsIdentities @Etale.{u} :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : P.IsLocalAtTarget (Scheme.precoverage @Etale) := ‹_›
  isStableUnderBaseChangeAgainst_of_isLocalAtTarget_precoverage P @Etale

/-- Specializes `isStableUnderBaseChangeAgainst_etale_of_isLocalAtTarget` to raw scheme morphism
predicates at `instances` transparency. -/
instance isStableUnderBaseChangeAgainst_etale_of_isLocalAtTarget'
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    [IsLocalAtTarget P Scheme.etalePrecoverage] : IsStableUnderBaseChangeAgainst P @Etale :=
  let P' : MorphismProperty Scheme.{u} := P
  have : P'.IsLocalAtTarget Scheme.etalePrecoverage := ‹_›
  isStableUnderBaseChangeAgainst_etale_of_isLocalAtTarget P'

/-- If `P` is local at the target for `Scheme.etalePrecoverage`, then `P` is preserved by base
change along any étale morphism. -/
theorem pullback_snd_of_etale_of_isLocalAtTarget {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {X Y V : Scheme.{u}} (f : X ⟶ Y) (e : V ⟶ Y)
    [Etale e] (hf : P f) : P (pullback.snd f e) :=
  have := IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong (P := P) e ‹Etale e›
  P.pullback_snd f e hf

/-- Pullback-square form of `pullback_snd_of_etale_of_isLocalAtTarget`. -/
theorem of_isPullback_of_etale_of_isLocalAtTarget {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {W X V Y : Scheme.{u}}
    {fst : W ⟶ X} {snd : W ⟶ V} {f : X ⟶ Y} {e : V ⟶ Y} [Etale e]
    (sq : IsPullback fst snd f e) (hf : P f) : P snd :=
  (IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong (P := P) e ‹Etale e›).of_isPullback
    sq hf

/-- If `P` respects precomposition with étale morphisms and is stable under base change along étale
morphisms, then on any commutative square `q ≫ f = h ≫ e` with `q` and `e` étale, `P f` implies
`P h`. -/
theorem of_etale_commSq {P : MorphismProperty Scheme.{u}}
    [P.RespectsLeft @Etale] [P.IsStableUnderBaseChangeAgainst @Etale]
    {U V X Y : Scheme.{u}} {f : X ⟶ Y} {h : U ⟶ V} (q : U ⟶ X) (e : V ⟶ Y)
    [Etale q] [Etale e] (w : q ≫ f = h ≫ e) (hf : P f) : P h := by
  let s : U ⟶ pullback f e := pullback.lift q h w
  have hs : s ≫ pullback.fst f e = q := pullback.lift_fst q h w
  have : Etale (s ≫ pullback.fst f e) := hs.symm ▸ ‹Etale q›
  have : Etale s := Etale.of_comp s (pullback.fst f e)
  have := IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong (P := P) e ‹Etale e›
  have hfst : P (pullback.snd f e) := P.pullback_snd f e hf
  simpa [s] using RespectsLeft.precomp (Q := @Etale) s ‹Etale s› (pullback.snd f e) hfst

/-- Auxiliary predicate for degree induction: every geometric fibre of `e : V ⟶ Y` is finite of
cardinality at most `d`. -/
private def BoundedGeometricFibers {V Y : Scheme.{u}} (e : V ⟶ Y) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Y),
    Finite {v : Spec (.of Ω) ⟶ V // v ≫ e = y} ∧
      Nat.card {v : Spec (.of Ω) ⟶ V // v ≫ e = y} ≤ d

/-- A standard étale morphism of affine schemes has bounded geometric fibres, bounded by the
degree of the defining monic polynomial. -/
private lemma boundedGeometricFibers_of_isStandardEtale {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardEtale R S] :
    ∃ d, BoundedGeometricFibers (Spec.algebraMap R S) d := by
  have Q : StandardEtalePresentation R S := Nonempty.some inferInstance
  refine ⟨Q.f.natDegree, fun Ω _ y ↦ ?_⟩
  classical
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  have hφ : Spec.map φ = Spec.algebraMap R Ω := rfl
  rw [hφ]
  let p : Polynomial Ω := Q.f.map φ.hom
  have hp : p ≠ 0 := (Q.monic_f.map φ.hom).ne_zero
  let evalX (v : {v : Spec (.of Ω) ⟶ Spec (.of S) //
      v ≫ Spec.algebraMap R S = Spec.algebraMap R Ω}) : p.roots.toFinset :=
    ⟨Spec.homEquivAlgHom v Q.x, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (by
      have hx : Polynomial.aeval (Spec.homEquivAlgHom v Q.x) Q.f = 0 := by
        rw [Polynomial.aeval_algHom_apply, Q.hasMap.1, map_zero]
      simpa [p, Polynomial.aeval_def, Polynomial.eval_map, RingHom.algebraMap_toAlgebra] using hx))⟩
  have hinj : Function.Injective evalX := fun v₁ v₂ h ↦
    Spec.homEquivAlgHom.injective (Q.hom_ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective evalX hinj, (Nat.card_le_card_of_injective evalX hinj).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (Multiset.toFinset_card_le p.roots).trans
    ((Polynomial.card_roots' p).trans Polynomial.natDegree_map_le)

/-- On the complement `W₂` of the diagonal in `V ×_O V`, the second projection `W₂ ⟶ V` has
strictly smaller geometric-fibre bound than `e' : V ⟶ O`. -/
private lemma boundedGeometricFibers_compl_diagonal {V O : Scheme.{u}} (e' : V ⟶ O)
    {d : ℕ} (hb : BoundedGeometricFibers e' (d + 1))
    (W₂ : (pullback e' e').Opens)
    (hW₂ : (W₂ : Set ↑(pullback e' e')) = (Set.range (pullback.diagonal e'))ᶜ) :
    BoundedGeometricFibers (W₂.ι ≫ pullback.snd e' e') d := by
  intro Ω _ y
  obtain ⟨hfin, hcard⟩ := hb Ω (y ≫ e')
  let y₀ : {v : Spec (.of Ω) ⟶ V // v ≫ e' = y ≫ e'} := ⟨y, rfl⟩
  let φ : {w : Spec (.of Ω) ⟶ W₂.toScheme // w ≫ (W₂.ι ≫ pullback.snd e' e') = y} →
      {v : {v : Spec (.of Ω) ⟶ V // v ≫ e' = y ≫ e'} // v ≠ y₀} := fun w ↦
    ⟨⟨w.val ≫ W₂.ι ≫ pullback.fst e' e', by
        calc
          (w.val ≫ W₂.ι ≫ pullback.fst e' e') ≫ e'
              = w.val ≫ W₂.ι ≫ (pullback.fst e' e' ≫ e') := by simp only [Category.assoc]
          _ = (w.val ≫ (W₂.ι ≫ pullback.snd e' e')) ≫ e' := by
            rw [pullback.condition]; simp only [Category.assoc]
          _ = y ≫ e' := by rw [w.property]⟩,
      fun heq ↦ by
        have hw : w.val ≫ W₂.ι = y ≫ pullback.diagonal e' := by
          apply pullback.hom_ext
          · have h₁ : w.val ≫ W₂.ι ≫ pullback.fst e' e' = y := congrArg Subtype.val heq
            rw [Category.assoc, h₁, Category.assoc, pullback.diagonal_fst, Category.comp_id]
          · rw [Category.assoc, w.property, Category.assoc, pullback.diagonal_snd,
              Category.comp_id]
        have hmem : W₂.ι (w.val default) ∈ (W₂ : Set ↑(pullback e' e')) :=
          W₂.range_ι ▸ Set.mem_range_self (w.val default)
        rw [hW₂] at hmem
        exact hmem ⟨y default, by
          simpa only [← Scheme.Hom.comp_apply] using
            congrArg (fun k : Spec (.of Ω) ⟶ pullback e' e' ↦ k default) hw.symm⟩⟩
  have hinj : Function.Injective φ := by
    intro w₁ w₂ h
    ext1
    have hι : w₁.val ≫ W₂.ι = w₂.val ≫ W₂.ι := by
      apply pullback.hom_ext
      · have h₁ : w₁.val ≫ W₂.ι ≫ pullback.fst e' e' = w₂.val ≫ W₂.ι ≫ pullback.fst e' e' :=
          congrArg (fun z ↦ z.val.val) h
        simpa only [Category.assoc] using h₁
      · simpa only [Category.assoc] using w₁.property.trans w₂.property.symm
    exact (cancel_mono W₂.ι).1 hι
  let _ := Fintype.ofFinite {v : Spec (.of Ω) ⟶ V // v ≫ e' = y ≫ e'}
  classical
  have hfin' : Finite {w : Spec (.of Ω) ⟶ W₂.toScheme // w ≫ (W₂.ι ≫ pullback.snd e' e') = y} :=
    Finite.of_injective φ hinj
  refine ⟨hfin', (Nat.card_le_card_of_injective φ hinj).trans ?_⟩
  have hsub : Fintype.card {v : {v : Spec (.of Ω) ⟶ V // v ≫ e' = y ≫ e'} // v ≠ y₀} =
      (Finset.univ.erase y₀).card :=
    Fintype.card_of_subtype (Finset.univ.erase y₀) (by simp)
  have herase : (Finset.univ.erase y₀).card + 1 =
      Fintype.card {v : Spec (.of Ω) ⟶ V // v ≫ e' = y ≫ e'} := by
    simpa only [Finset.card_univ] using Finset.card_erase_add_one (Finset.mem_univ y₀)
  rw [Nat.card_eq_fintype_card] at hcard ⊢
  omega

/-- Factor an étale separated morphism `e : V ⟶ Y` with geometric fibres bounded by `d` through its
open image `O = e(V) ⊆ Y`, yielding an étale, separated, surjective morphism `e' : V ⟶ O` with the
same fibre bound. -/
private lemma exists_etale_surjective_factorization {V Y : Scheme.{u}} (e : V ⟶ Y)
    [Etale e] [IsSeparated e] {d : ℕ} (hb : BoundedGeometricFibers e d) :
    ∃ (O : Y.Opens) (e' : V ⟶ O.toScheme),
      Etale e' ∧ IsSeparated e' ∧ Surjective e' ∧ e' ≫ O.ι = e ∧ BoundedGeometricFibers e' d := by
  let O : Y.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
  have hO : Set.range e ⊆ Set.range O.ι := O.range_ι.ge
  let e' : V ⟶ O.toScheme := IsOpenImmersion.lift O.ι e hO
  have he' : e' ≫ O.ι = e := IsOpenImmersion.lift_fac O.ι e hO
  have : Etale (e' ≫ O.ι) := he'.symm ▸ ‹Etale e›
  have het : Etale e' := Etale.of_comp e' O.ι
  have : IsSeparated (e' ≫ O.ι) := he'.symm ▸ ‹IsSeparated e›
  have hsep : IsSeparated e' := IsSeparated.of_comp e' O.ι
  have hsurj : Surjective e' := ⟨fun y ↦ by
    obtain ⟨v, hv⟩ : y.val ∈ Set.range e := y.property
    refine ⟨v, O.ι.isOpenEmbedding.injective ?_⟩
    calc
      O.ι (e' v) = (e' ≫ O.ι) v := by rw [Scheme.Hom.comp_apply]
      _ = e v := by rw [he']
      _ = y.val := hv
      _ = O.ι y := rfl⟩
  have hb' : BoundedGeometricFibers e' d := by
    intro Ω _ y
    obtain ⟨hfin, hcard⟩ := hb Ω (y ≫ O.ι)
    let ψ : {v : Spec (.of Ω) ⟶ V // v ≫ e' = y} →
        {v : Spec (.of Ω) ⟶ V // v ≫ e = y ≫ O.ι} :=
      fun v ↦ ⟨v.val, by rw [← he', ← Category.assoc, v.property]⟩
    have hinj : Function.Injective ψ := fun _ _ h ↦
      Subtype.ext (congrArg (fun z ↦ z.val) h)
    exact ⟨Finite.of_injective ψ hinj, (Nat.card_le_card_of_injective ψ hinj).trans hcard⟩
  exact ⟨O, e', het, hsep, hsurj, he', hb'⟩

/-- Auxiliary induction on the geometric-fibre bound `d`: if `e : V ⟶ Y` is étale, separated, and
has geometric fibres of cardinality at most `d`, then `P h` implies `P (h ≫ e)`. -/
private lemma prop_comp_of_boundedGeometricFibers {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] :
    ∀ (d : ℕ) {U V Y : Scheme.{u}} (h : U ⟶ V) (e : V ⟶ Y) [Etale e] [IsSeparated e],
      BoundedGeometricFibers e d → P h → P (h ≫ e)
  | 0, U, V, _, h, e, _, _, hb, _ => by
      have : IsEmpty V := ⟨fun v ↦ by
        let x : Spec (V.residueField v) ⟶ V := V.fromSpecResidueField v
        obtain ⟨hfin, hle⟩ := hb (V.residueField v) (x ≫ e)
        have hpos : 0 < Nat.card {w : Spec (V.residueField v) ⟶ V // w ≫ e = x ≫ e} :=
          @Nat.card_pos _ ⟨⟨x, rfl⟩⟩ hfin
        exact absurd (hpos.trans_le hle) (lt_irrefl 0)⟩
      have : IsEmpty U := Function.isEmpty h.base
      exact of_isEmpty_of_isLocalAtSource_precoverage @IsOpenImmersion (h ≫ e)
  | d + 1, _, V, _, h, e, _, _, hb, hh => by
      obtain ⟨O, e', _, _, hsurj, he', hb'⟩ := exists_etale_surjective_factorization e hb
      rw [← he', ← Category.assoc]
      refine RespectsRight.postcomp (Q := @IsOpenImmersion) O.ι inferInstance (h ≫ e') ?_
      have hcov : Presieve.singleton e' ∈ Scheme.etalePrecoverage O.toScheme :=
        (Scheme.singleton_mem_precoverage_iff (P := @Etale) e').2 ⟨hsurj.surj, inferInstance⟩
      refine IsLocalAtTarget.of_forall_pullbackSnd hcov ?_
      rintro _ _ _ ⟨⟩
      let Δ : V ⟶ pullback e' e' := pullback.diagonal e'
      let W₂ : (pullback e' e').Opens := ⟨(Set.range Δ)ᶜ, Δ.isClosedMap.isClosed_range.isOpen_compl⟩
      let q : pullback (h ≫ e') e' ⟶ pullback e' e' :=
        pullback.map (h ≫ e') e' e' e' h (𝟙 V) (𝟙 O.toScheme) (by simp) (by simp)
      refine IsZariskiLocalAtSource.of_pullback_pair q Δ W₂.ι
        (fun z ↦ (em (z ∈ Set.range Δ)).imp_right fun hz ↦ W₂.range_ι.ge hz) ?_ ?_
      · have sq₁ := (pullback_lift_diagonal_isPullback h e').flip
        rw [← P.cancel_left_of_respectsIso sq₁.isoPullback.hom, ← Category.assoc,
          sq₁.isoPullback_hom_fst]
        simpa using hh
      · have sq_q : IsPullback q (pullback.fst (h ≫ e') e') (pullback.fst e' e') h :=
          IsPullback.of_right (by simpa [q] using (IsPullback.of_hasPullback (h ≫ e') e').flip)
            (by simp [q]) (IsPullback.of_hasPullback e' e').flip
        have sq₂ : IsPullback (pullback.fst q W₂.ι ≫ pullback.fst (h ≫ e') e')
            (pullback.snd q W₂.ι) h (W₂.ι ≫ pullback.fst e' e') :=
          ((IsPullback.of_hasPullback q W₂.ι).flip.paste_vert sq_q).flip
        have hfac₂ : pullback.fst q W₂.ι ≫ pullback.snd (h ≫ e') e' =
            pullback.snd q W₂.ι ≫ (W₂.ι ≫ pullback.snd e' e') := by
          have hqsnd : q ≫ pullback.snd e' e' = pullback.snd (h ≫ e') e' := by simp [q]
          rw [← hqsnd, ← Category.assoc, pullback.condition, Category.assoc]
        rw [hfac₂]
        exact prop_comp_of_boundedGeometricFibers d (pullback.snd q W₂.ι)
          (W₂.ι ≫ pullback.snd e' e') (boundedGeometricFibers_compl_diagonal e' hb' W₂ rfl)
          (of_isPullback_of_etale_of_isLocalAtTarget sq₂ hh)

/-- Around any point `v : V` of an étale morphism `e : V ⟶ Y`, find affine open neighbourhoods on
which `e` restricts to a standard étale morphism of affine schemes, hence is separated with bounded
geometric fibres. -/
private lemma exists_standardEtale_open_nhds {V Y : Scheme.{u}} (e : V ⟶ Y) [Etale e] (v : V) :
    ∃ (W_V W_Y : Scheme.{u}) (jV : W_V ⟶ V) (_ : IsOpenImmersion jV) (jY : W_Y ⟶ Y)
      (e₀ : W_V ⟶ W_Y) (d : ℕ),
      IsOpenImmersion jY ∧ Etale e₀ ∧ IsSeparated e₀ ∧
        v ∈ jV.opensRange ∧ jV ≫ e = e₀ ≫ jY ∧ BoundedGeometricFibers e₀ d := by
  obtain ⟨_, ⟨U_Y, hUY, rfl⟩, hvY, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e v)) isOpen_univ
  obtain ⟨_, ⟨U_V, hUV, rfl⟩, hvV, hle : U_V ≤ e ⁻¹ᵁ U_Y⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hvY (e ⁻¹ᵁ U_Y).is_open'
  replace hUY : IsAffineOpen U_Y := hUY
  replace hUV : IsAffineOpen U_V := hUV
  have het : (e.appLE U_Y U_V hle).hom.Etale := e.etale_appLE hUY hUV hle
  algebraize [(e.appLE U_Y U_V hle).hom]
  have : Algebra.Etale Γ(Y, U_Y) Γ(V, U_V) := RingHom.etale_algebraMap.mp het
  have : Algebra.IsEtaleAt Γ(Y, U_Y) (hUV.primeIdealOf ⟨v, hvV⟩).asIdeal :=
    Algebra.FormallyEtale.comp Γ(Y, U_Y) Γ(V, U_V)
      (Localization.AtPrime (hUV.primeIdealOf ⟨v, hvV⟩).asIdeal)
  obtain ⟨g, hg, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := Γ(Y, U_Y)) (hUV.primeIdealOf ⟨v, hvV⟩).asIdeal
  let jg : Spec (.of (Localization.Away g)) ⟶ Spec Γ(V, U_V) :=
    Spec.algebraMap Γ(V, U_V) (Localization.Away g)
  have : IsOpenImmersion jg :=
    inferInstanceAs (IsOpenImmersion (Spec.algebraMap Γ(V, U_V) (Localization.Away g)))
  let jV : Spec (.of (Localization.Away g)) ⟶ V := jg ≫ hUV.fromSpec
  have : IsOpenImmersion jV := inferInstanceAs (IsOpenImmersion (jg ≫ hUV.fromSpec))
  have hjV_mem : v ∈ jV.opensRange := by
    obtain ⟨z, hz⟩ : hUV.primeIdealOf ⟨v, hvV⟩ ∈ jg.opensRange := by
      rw [Scheme.Hom.opensRange_localizationAway]; exact hg
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hUV.fromSpec_primeIdealOf]⟩
  let e₀ : Spec (.of (Localization.Away g)) ⟶ Spec Γ(Y, U_Y) :=
    Spec.algebraMap Γ(Y, U_Y) (Localization.Away g)
  have he₀ : Etale e₀ :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  obtain ⟨d, hd⟩ := boundedGeometricFibers_of_isStandardEtale
    (R := Γ(Y, U_Y)) (S := Localization.Away g)
  have hcomm : jV ≫ e = e₀ ≫ hUY.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec e hUY hUV hle, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
  exact ⟨_, _, jV, inferInstance, hUY.fromSpec, e₀, d, inferInstance, he₀, inferInstance,
    hjV_mem, hcomm, hd⟩

/-- Auxiliary proof of postcomposition with étale morphisms for `respectsRight_etale_of_isLocal`. -/
private lemma postcomp_etale_of_isLocal {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] {U V Y : Scheme.{u}} {h : U ⟶ V} (e : V ⟶ Y) [Etale e]
    (hh : P h) : P (h ≫ e) := by
  have hloc : ∀ u : U, ∃ (W_U : Scheme.{u}) (p : W_U ⟶ U),
      IsOpenImmersion p ∧ u ∈ Set.range p ∧ P (p ≫ (h ≫ e)) := fun u ↦ by
    obtain ⟨_, _, jV, _, jY, e₀, d, _, _, _, hjV_mem, hcomm, hd⟩ :=
      exists_standardEtale_open_nhds e (h u)
    have hh' : P (pullback.snd h jV) := pullback_snd_of_etale_of_isLocalAtTarget h jV hh
    refine ⟨pullback h jV, pullback.fst h jV, inferInstance, ?_, ?_⟩
    · simpa [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_pullbackFst] using hjV_mem
    · rw [← Category.assoc, pullback.condition, Category.assoc, hcomm, ← Category.assoc]
      exact RespectsRight.postcomp (Q := @IsOpenImmersion) jY inferInstance _
        (prop_comp_of_boundedGeometricFibers d (pullback.snd h jV) e₀ hd hh')
  choose W_U p _ hmem hP using hloc
  exact IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers U W_U p fun u ↦ ⟨u, hmem u⟩) hP

/-- **Stacks, Lemma 35.32.6 (04R2), postcomposition half.** If `P` is Zariski-local at the source,
local at the target for `Scheme.etalePrecoverage`, and respects postcomposition with open
immersions, then `P` respects postcomposition with arbitrary étale morphisms. -/
@[stacks 04R2 "postcomposition with étale morphisms"]
theorem respectsRight_etale_of_isLocal (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] : P.RespectsRight @Etale where
  postcomp e _ _ hh := postcomp_etale_of_isLocal e hh

/-- **Stacks, Lemma 35.32.6 (04R2), composition with étale morphisms.** If `P` is local at the
source and at the target for `Scheme.etalePrecoverage` and respects postcomposition with open
immersions, then `P` respects composition with étale morphisms on both sides. -/
@[stacks 04R2]
theorem respects_etale_of_isLocal (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] : P.Respects @Etale :=
  have := isZariskiLocalAtSource_of_etalePrecoverage P
  { toRespectsLeft := inferInstance
    toRespectsRight := respectsRight_etale_of_isLocal P }

/-- **Stacks, Lemma 35.32.6 (04R2), descent on étale-surjective squares.** Let `q ≫ f = h ≫ e` be
a commutative square of schemes with `q` étale and surjective and `e` étale. If `P` is local at the
source and at the target for `Scheme.etalePrecoverage` and respects postcomposition with open
immersions, then `P h` implies `P f`. -/
@[stacks 04R2 "descent along étale-surjective squares"]
theorem of_etale_surjective_commSq {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion]
    {U V X Y : Scheme.{u}} {f : X ⟶ Y} {h : U ⟶ V} (q : U ⟶ X) (e : V ⟶ Y)
    [Etale q] [Surjective q] [Etale e] (w : q ≫ f = h ≫ e) (hh : P h) : P f := by
  have := isZariskiLocalAtSource_of_etalePrecoverage P
  have hhe : P (h ≫ e) := (respectsRight_etale_of_isLocal P).postcomp e ‹_› h hh
  have hqf : P (q ≫ f) := w.symm ▸ hhe
  have hcov : Presieve.singleton q ∈ Scheme.etalePrecoverage X :=
    (Scheme.singleton_mem_precoverage_iff (P := @Etale) q).2 ⟨‹Surjective q›.surj, ‹Etale q›⟩
  exact IsLocalAtSource.of_forall_comp hcov (by rintro _ _ ⟨⟩; exact hqf)

/-- **Stacks, Lemma 35.32.6 (04R2), equivalence on étale-surjective squares.** Let
`q ≫ f = h ≫ e` be a commutative square of schemes with `q` étale and surjective and `e` étale.
If `P` is local at the source and at the target for `Scheme.etalePrecoverage` and respects
postcomposition with open immersions, then `P f ↔ P h`. -/
@[stacks 04R2]
theorem iff_of_etale_surjective_commSq (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion]
    {U V X Y : Scheme.{u}} {f : X ⟶ Y} {h : U ⟶ V} (q : U ⟶ X) (e : V ⟶ Y)
    [Etale q] [Surjective q] [Etale e] (w : q ≫ f = h ≫ e) : P f ↔ P h :=
  ⟨of_etale_commSq q e w, of_etale_surjective_commSq q e w⟩

end CategoryTheory.MorphismProperty
