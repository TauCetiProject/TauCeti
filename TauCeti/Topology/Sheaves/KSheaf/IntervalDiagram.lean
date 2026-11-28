/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.Algebra.Homology.OrderedCech.IntervalDiagram
public import TauCeti.Topology.Sheaves.KSheaf.Total

/-!
# Totals of interval diagrams of homotopy K-sheaves

Let `S` be a finite partially ordered set and `F` a K-presheaf on `X` of interval diagrams on `S`
of chain complexes: for each compact set `K` an interval diagram `F(K)`, whose value `F(K)[s, t]`
on an interval `s ≤ t` is a chain complex, restricting functorially in `K`. Its flag total
`K ↦ Tot F(K)` (`TauCeti.IntervalDiagram.totalFunctor`) is the finite homotopy colimit that glues
the local virtual complexes of an implicit atlas into its virtual cochain complex. Read in cochain
degrees `N - •` through the embedding `n ↦ N - n` (`ComplexShape.embeddingUpIntLE N`), as the
relative chains of an atlas are, it is a K-presheaf of cochain complexes.

**Pardon's Lemma A.8.1**
(`TopCat.KPresheaf.isHomotopyKSheaf_comp_intervalDiagramTotalFunctor_comp_extendFunctor`): if every
value `K ↦ F(K)[s, t]`, read in cochain degrees `M - •`, is a homotopy K-sheaf for every `M`, then
so is the total, read in cochain degrees `N - •`. The flag total of `F(K)` is the total complex of
its flag complex, a first-quadrant bicomplex whose column `p` is the coproduct of the
`F(K)[s₀, sₚ]` over the flags `s₀ < ⋯ < sₚ` (`TauCeti.IntervalDiagram.isColimitFlagComplexCofan`).
Flipping it (`TauCeti.IntervalDiagram.totalFunctorIsoFlip`), the columns become the rows, there
are finitely many of them since `S` is finite, and each is a finite coproduct of homotopy
K-sheaves (`TopCat.KPresheaf.isHomotopyKSheaf_of_isColimit_cofan`). The total of a first-quadrant
bicomplex with finitely many rows of homotopy K-sheaves is a homotopy K-sheaf
(`TopCat.KPresheaf.isHomotopyKSheaf_comp_homologicalComplex₂TotalFunctor_comp_extendFunctor`).

The flag length `p` lowers the cochain degree by `p`, so the row `p` is read in cochain degrees
`N - p - •`; this is why the hypothesis is asked for every reading `M - •` of the values.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. **20** (2016), 779–1034, Appendix A.7 (interval
  diagrams, Definition A.7.2) and Appendix A.8 (Lemma A.8.1).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace ComplexShape Finset TauCeti
open TauCeti.IntervalDiagram

universe w w' v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]
  [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]
  {S : Type w'} [PartialOrder S] [HasCoproducts.{w'} C]

variable (F : KPresheaf (IntervalDiagram S (ChainComplex C ℕ)) X)

omit [T2Space X] [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
  [WeaklyLocallyCompactSpace X] in
/-- The row `q` of the flipped flag bicomplexes of `F`, read in cochain degrees `M - •`, as the
cofan of the values `K ↦ F(K)[s₀, s_q]` over the flags `s₀ < ⋯ < s_q`. -/
private noncomputable def flagRowCofan (q : ℕ) (M : ℤ) :
    Cofan fun s : {s : Finset (LinearExtension S) // IsFlag s ∧ #s = q + 1} ↦
      F ⋙ (evaluation _ _).obj (op (flagInterval s.property.1)) ⋙
        (embeddingUpIntLE M).extendFunctor C :=
  Cofan.mk (F ⋙ flagComplexFunctor S (ChainComplex C ℕ) ⋙
      HomologicalComplex₂.flipFunctor C (down ℕ) (down ℕ) ⋙
        (HomologicalComplex.eval C (down ℕ) q).mapHomologicalComplex (down ℕ) ⋙
          (embeddingUpIntLE M).extendFunctor C)
    fun s ↦
      { app K := ((embeddingUpIntLE M).extendFunctor C).map
          ((F.obj K).flagComplexι s.property.1 s.property.2)
        -- the map of the row `q` of the flipped flag bicomplexes is the component `q` of the map of
        -- flag complexes, on which `flagComplexι_flagComplexMap_f` acts summand by summand
        naturality _ _ h :=
          (((embeddingUpIntLE M).extendFunctor C).map_comp _ _).symm.trans <|
            (congrArg ((embeddingUpIntLE M).extendFunctor C).map
              (flagComplexι_flagComplexMap_f (F.map h) s.property.1 s.property.2).symm).trans
                (((embeddingUpIntLE M).extendFunctor C).map_comp _ _) }

omit [T2Space X] [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
  [WeaklyLocallyCompactSpace X] in
/-- The row `q` of the flipped flag bicomplexes of `F` is the coproduct of the values of `F` over
the flags with `q + 1` vertices, at every compact set, so as a K-presheaf. -/
private noncomputable def isColimitFlagRowCofan (q : ℕ) (M : ℤ) :
    IsColimit (flagRowCofan F q M) :=
  evaluationJointlyReflectsColimits _ fun K ↦ (isColimitMapCoconeCofanMkEquiv _ _ _).symm <|
    isColimitMapCoconeCofanMkEquiv ((embeddingUpIntLE M).extendFunctor C) _ _ <|
      isColimitOfPreserves ((embeddingUpIntLE M).extendFunctor C)
        ((F.obj K).isColimitFlagComplexCofan q)

/-- **The total of an interval diagram of homotopy K-sheaves is a homotopy K-sheaf** (Pardon,
Lemma A.8.1). Let `S` be a finite partially ordered set and `F` a K-presheaf of interval diagrams
on `S` of chain complexes. If for every interval `I` of `S` and every integer `M` the values
`K ↦ F(K)[I]`, read in cochain degrees `M - •`, form a homotopy K-sheaf, then the flag totals
`K ↦ Tot F(K)`, read in cochain degrees `N - •`, form a homotopy K-sheaf. -/
theorem isHomotopyKSheaf_comp_intervalDiagramTotalFunctor_comp_extendFunctor [Finite S]
    (hF : ∀ (I : NonemptyInterval S) (M : ℤ), IsHomotopyKSheaf
      (F ⋙ (evaluation _ _).obj (op I) ⋙ (embeddingUpIntLE M).extendFunctor C))
    (N : ℤ) :
    IsHomotopyKSheaf
      (F ⋙ IntervalDiagram.totalFunctor S C ⋙ (embeddingUpIntLE N).extendFunctor C) := by
  have := Fintype.ofFinite (LinearExtension S)
  -- The rows of the flipped flag bicomplexes are its columns, which vanish from the cardinality
  -- of `S` on and are finite coproducts of the values of `F`.
  refine (isHomotopyKSheaf_comp_homologicalComplex₂TotalFunctor_comp_extendFunctor
    (F ⋙ flagComplexFunctor S (ChainComplex C ℕ) ⋙
      HomologicalComplex₂.flipFunctor C (down ℕ) (down ℕ))
    (Fintype.card (LinearExtension S)) N (fun K p q hq ↦ ?_) fun q _ ↦ ?_).of_iso
      (Functor.isoWhiskerLeft F (Functor.isoWhiskerRight (totalFunctorIsoFlip S C) _)).symm
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((F.obj K).flagFunctor.isZero_orderedCechComplex_X hq)
  · exact isHomotopyKSheaf_of_isColimit_cofan (isColimitFlagRowCofan F q (N - q)) fun s ↦
      hF _ _

end TopCat.KPresheaf
