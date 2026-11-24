/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic

import TauCeti.AlgebraicTopology.SimplexCategory.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
import TauCeti.CategoryTheory.Limits.Shapes.Products

/-!
# Nondegenerate chains for homology of a category with functor coefficients

For a category `C` and `M : C ⥤ A`, every epimorphism `φ : ⦋n⦌ ⟶ ⦋m⦌` in `SimplexCategory` fixes
`0`, so `categorySimplicialObject M` admits a canonical splitting
`TauCeti.categorySimplicialObjectSplitting M` indexed by `(nerve C).nonDegenerate n`. When `A` is
preadditive, the associated complex `TauCeti.nondegCategoryChainComplex M`, with degree `n` equal
to `∐_{σ ∈ (nerve C).nonDegenerate n} M.obj (σ.obj 0)`, is chain homotopy equivalent to
`categoryChainComplex M` (`TauCeti.homotopyEquivNondegCategoryChainComplex`), vanishes on
degenerate nerve simplices (`TauCeti.ιNondegCategoryChainComplex_eq_zero`), and computes
`categoryHomology M n` (`TauCeti.nondegCategoryHomologyIso`). When `A` is abelian it is isomorphic
to the Dold–Kan normalized complex `TauCeti.normalizedCategoryChainComplex M`
(`TauCeti.nondegCategoryChainComplexIsoNormalized`).

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
-/

public noncomputable section

universe v v' u u'

open CategoryTheory Limits Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial

namespace TauCeti

section Splitting

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasCoproducts.{max u v} A]

/-- Canonical `SimplicialObject.Splitting` of `categorySimplicialObject M` indexed by
`(nerve C).nonDegenerate n`. -/
def categorySimplicialObjectSplitting (M : C ⥤ A) :
    (categorySimplicialObject M).Splitting where
  N n := ∐ fun y : (nerve C).nonDegenerate n ↦ M.obj ((y.val : ComposableArrows C n).obj 0)
  ι n := Sigma.desc fun y ↦ ιCategorySimplicial M y.val
  isColimit' := fun ⟨⟨n⟩⟩ ↦ by
    let hc := ((nerve C).splitting.cofan (op ⦋n⦌)).isColimit_cofanTypes_iff.mpr
      ⟨(nerve C).splitting.isColimit (op ⦋n⦌)⟩
    let e : (Σ I : SimplicialObject.Splitting.IndexSet (op ⦋n⦌),
        (nerve C).nonDegenerate I.1.unop.len) ≃ ComposableArrows C n :=
      CofanTypes.equivOfIsColimit hc
    -- `((nerve C).splitting.cofan (op ⦋n⦌)).cofanTypes.inj I` applies `(nerve C).map I.e.op`.
    have he (I : SimplicialObject.Splitting.IndexSet (op ⦋n⦌))
        (y : (nerve C).nonDegenerate I.1.unop.len) : e ⟨I, y⟩ = (nerve C).map I.e.op y.val :=
      CofanTypes.equivOfIsColimit_apply hc I y
    have hEq (p : Σ I : SimplicialObject.Splitting.IndexSet (op ⦋n⦌),
        (nerve C).nonDegenerate I.1.unop.len) :
        M.obj ((p.2.val : ComposableArrows C p.1.1.unop.len).obj 0) = M.obj ((e p).obj 0) :=
      congrArg M.obj (((congrArg (·.obj 0) (he p.1 p.2)).trans
        (CategoryTheory.nerve.map_obj p.1.e p.2.val 0)).trans
          (congrArg (p.2.val : ComposableArrows C _).obj
            (SimplexCategory.toOrderHom_zero_of_epi p.1.e))).symm
    refine (SimplicialObject.Splitting.cofan' _ _ _ (op ⦋n⦌)).isColimitOfIsColimitSigma
      (fun I y ↦ Sigma.ι (fun z : (nerve C).nonDegenerate I.1.unop.len ↦
        M.obj ((z.val : ComposableArrows C I.1.unop.len).obj 0)) y)
      (fun _ ↦ coproductIsCoproduct _) ?_
    refine IsColimit.ofIsoColimit
      ((categorySimplicialObjectXCofan M n).isColimitOfEquiv
        (isColimitCategorySimplicialObjectXCofan M n) e fun p ↦ eqToIso (hEq p))
      (Cofan.ext (Iso.refl _) fun ⟨I, y⟩ ↦ ?_)
    dsimp only [Cofan.mk_pt, Limits.cofan_mk_inj, SimplicialObject.Splitting.cofan', Iso.refl_hom,
      eqToIso.hom]
    exact (Category.comp_id _).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (categorySimplicialObject M).map I.e.op)
        (Sigma.ι_comp_desc (fun z : (nerve C).nonDegenerate I.1.unop.len ↦
          ιCategorySimplicial M z.val) y))).trans
      (ιCategorySimplicial_map_of_epi M I.e y.val)).symm

end Splitting

section Nondeg

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

/-- The chain complex of nondegenerate simplices computing homology of `C` with coefficients in
`M : C ⥤ A`, with degree `n` equal to `∐_{σ ∈ (nerve C).nonDegenerate n} M.obj (σ.obj 0)`. -/
def nondegCategoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (categorySimplicialObjectSplitting M).nondegComplex

/-- The split epimorphism `categoryChainComplex M ⟶ nondegCategoryChainComplex M`. -/
def toNondegCategoryChainComplex (M : C ⥤ A) :
    categoryChainComplex M ⟶ nondegCategoryChainComplex M :=
  (categorySimplicialObjectSplitting M).toNondegComplex

/-- The split monomorphism `nondegCategoryChainComplex M ⟶ categoryChainComplex M`. -/
def fromNondegCategoryChainComplex (M : C ⥤ A) :
    nondegCategoryChainComplex M ⟶ categoryChainComplex M :=
  (categorySimplicialObjectSplitting M).fromNondegComplex

/-- Chain homotopy equivalence between `categoryChainComplex M` and
`nondegCategoryChainComplex M`. -/
def homotopyEquivNondegCategoryChainComplex (M : C ⥤ A) :
    HomotopyEquiv (categoryChainComplex M) (nondegCategoryChainComplex M) :=
  (categorySimplicialObjectSplitting M).homotopyEquivNondegComplex

@[simp, reassoc] lemma PInfty_toNondegCategoryChainComplex (M : C ⥤ A) :
    (PInfty : categoryChainComplex M ⟶ categoryChainComplex M) ≫ toNondegCategoryChainComplex M =
      toNondegCategoryChainComplex M :=
  SimplicialObject.Splitting.PInfty_toNondegComplex _

@[simp, reassoc] lemma PInfty_f_toNondegCategoryChainComplex_f (M : C ⥤ A) (n : ℕ) :
    (PInfty : categoryChainComplex M ⟶ categoryChainComplex M).f n ≫
        (toNondegCategoryChainComplex M).f n = (toNondegCategoryChainComplex M).f n :=
  (HomologicalComplex.comp_f _ _ n).symm.trans
    (HomologicalComplex.congr_hom (PInfty_toNondegCategoryChainComplex M) n)

instance isSplitEpi_toNondegCategoryChainComplex (M : C ⥤ A) :
    IsSplitEpi (toNondegCategoryChainComplex M) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

instance isSplitMono_fromNondegCategoryChainComplex (M : C ⥤ A) :
    IsSplitMono (fromNondegCategoryChainComplex M) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)] lemma fromNondegCategoryChainComplex_toNondegCategoryChainComplex
    (M : C ⥤ A) :
    fromNondegCategoryChainComplex M ≫ toNondegCategoryChainComplex M = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]
lemma fromNondegCategoryChainComplex_f_toNondegCategoryChainComplex_f (M : C ⥤ A) (n : ℕ) :
    (fromNondegCategoryChainComplex M).f n ≫ (toNondegCategoryChainComplex M).f n =
      𝟙 _ := by simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)] lemma toNondegCategoryChainComplex_fromNondegCategoryChainComplex
    (M : C ⥤ A) :
    toNondegCategoryChainComplex M ≫ fromNondegCategoryChainComplex M =
      (PInfty : categoryChainComplex M ⟶ categoryChainComplex M) :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]
lemma toNondegCategoryChainComplex_f_fromNondegCategoryChainComplex_f (M : C ⥤ A) (n : ℕ) :
    (toNondegCategoryChainComplex M).f n ≫ (fromNondegCategoryChainComplex M).f n =
      (PInfty : categoryChainComplex M ⟶ categoryChainComplex M).f n := by
  simp [← HomologicalComplex.comp_f]

@[simp] lemma homotopyEquivNondegCategoryChainComplex_hom (M : C ⥤ A) :
    (homotopyEquivNondegCategoryChainComplex M).hom =
      toNondegCategoryChainComplex M := (rfl)

@[simp] lemma homotopyEquivNondegCategoryChainComplex_inv (M : C ⥤ A) :
    (homotopyEquivNondegCategoryChainComplex M).inv =
      fromNondegCategoryChainComplex M := (rfl)

/-- Generator morphism `M.obj (σ.obj 0) ⟶ (nondegCategoryChainComplex M).X n` attached to
`σ : ComposableArrows C n`. -/
def ιNondegCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (nondegCategoryChainComplex M).X n :=
  ιCategoryChainComplex M σ ≫ (toNondegCategoryChainComplex M).f n

/-- Alternating face boundary formula in `nondegCategoryChainComplex M`. -/
@[reassoc] lemma ιNondegCategoryChainComplex_d (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιNondegCategoryChainComplex M σ ≫ (nondegCategoryChainComplex M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          ιNondegCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          ιNondegCategoryChainComplex M ((nerve C).δ j.succ σ) := by
  have hc : ιNondegCategoryChainComplex M σ ≫
      (nondegCategoryChainComplex M).d (n + 1) n =
      (ιCategoryChainComplex M σ ≫ (categoryChainComplex M).d (n + 1) n) ≫
        (toNondegCategoryChainComplex M).f n := by
    dsimp only [ιNondegCategoryChainComplex]
    rw [Category.assoc, (toNondegCategoryChainComplex M).comm (n + 1) n, Category.assoc]
  refine hc.trans ((congrArg (· ≫ _) (ιCategoryChainComplex_d M σ)).trans ?_)
  exact (Preadditive.add_comp _ _ _ _ _ _).trans (congrArg₂ (· + ·) (Category.assoc _ _ _)
    ((Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      Preadditive.zsmul_comp _ _ _)))

/-- `ιNondegCategoryChainComplex M σ` vanishes whenever `σ` is a degenerate nerve simplex. -/
lemma ιNondegCategoryChainComplex_eq_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n)
    (hσ : σ ∈ (nerve C).degenerate n) : ιNondegCategoryChainComplex M σ = 0 := by
  obtain _ | n := n
  · exact (SSet.degenerate_zero _ ▸ hσ).elim
  · -- Bind `σ` at type `(nerve C) _⦋n + 1⦌` (defeq to `ComposableArrows C (n + 1)` by `nerve_obj`).
    let σ' : (nerve C) _⦋n + 1⦌ := σ
    have hσ' : σ' ∈ (nerve C).degenerate (n + 1) := hσ
    rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hσ'
    obtain ⟨i, τ, hτ⟩ := hσ'
    let τ' : ComposableArrows C n := τ
    have hτ' : ((nerve C).σ i τ' : ComposableArrows C (n + 1)) = σ := hτ
    have h0 : ιCategoryChainComplex M ((nerve C).σ i τ') ≫
        (PInfty : categoryChainComplex M ⟶ categoryChainComplex M).f (n + 1) = 0 :=
      (congrArg (· ≫ _) (ιCategoryChainComplex_eq M _)).trans
        ((ιCategorySimplicial_σ_assoc M i τ' _).symm.trans
          ((congrArg (_ ≫ ·) (σ_comp_PInfty (categorySimplicialObject M) i)).trans comp_zero))
    have h1 : ιNondegCategoryChainComplex M ((nerve C).σ i τ') = 0 :=
      (congrArg (ιCategoryChainComplex M _ ≫ ·)
        (PInfty_f_toNondegCategoryChainComplex_f M (n + 1)).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h0).trans zero_comp))
    exact hτ' ▸ h1

private lemma ιNondegCategoryChainComplex_eq_ι (M : C ⥤ A) {n : ℕ}
    (y : (nerve C).nonDegenerate n) : ιNondegCategoryChainComplex M y.val =
      Sigma.ι (fun z : (nerve C).nonDegenerate n ↦
        M.obj ((z.val : ComposableArrows C n).obj 0)) y := by
  refine (congrArg (· ≫ (toNondegCategoryChainComplex M).f n)
    (ιCategoryChainComplex_eq M y.val)).trans ?_
  let s := categorySimplicialObjectSplitting M
  have hs : s.ι n ≫ (toNondegCategoryChainComplex M).f n = 𝟙 (s.N n) :=
    (congrArg (s.ι n ≫ ·) (PInfty_f_toNondegCategoryChainComplex_f M n)).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (s.fromNondegComplex_f n).symm).trans
        (fromNondegCategoryChainComplex_f_toNondegCategoryChainComplex_f M n)))
  exact (congrArg (· ≫ (toNondegCategoryChainComplex M).f n)
    (Sigma.ι_comp_desc (fun z : (nerve C).nonDegenerate n ↦
      ιCategorySimplicial M z.val) y)).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (Sigma.ι _ y ≫ ·) hs).trans (Category.comp_id _)))

/-- Cofan presenting `(nondegCategoryChainComplex M).X n` over `(nerve C).nonDegenerate n`. -/
abbrev cofanNondegCategoryChainComplex (M : C ⥤ A) (n : ℕ) :
    Cofan (fun y : (nerve C).nonDegenerate n ↦ M.obj ((y.val : ComposableArrows C n).obj 0)) :=
  Cofan.mk ((nondegCategoryChainComplex M).X n)
    (fun y ↦ ιNondegCategoryChainComplex M y.val)

/-- `cofanNondegCategoryChainComplex M n` is a coproduct colimit. -/
def isColimitCofanNondegCategoryChainComplex (M : C ⥤ A) (n : ℕ) :
    IsColimit (cofanNondegCategoryChainComplex M n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) fun y ↦
      (Category.comp_id _).trans (ιNondegCategoryChainComplex_eq_ι M y).symm)

@[ext] lemma nondegCategoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (nondegCategoryChainComplex M).X n ⟶ T}
    (h : ∀ (σ : ComposableArrows C n), σ ∈ (nerve C).nonDegenerate n →
      ιNondegCategoryChainComplex M σ ≫ f = ιNondegCategoryChainComplex M σ ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitCofanNondegCategoryChainComplex M n) _ _ fun ⟨σ, hσ⟩ ↦
    h σ hσ

/-- Isomorphism onto degree-`n` nondegenerate chains when `(nerve C).nonDegenerate n` is
`Unique`. -/
def nondegCategoryChainComplexXIsoOfUnique (M : C ⥤ A) (n : ℕ)
    [Unique ((nerve C).nonDegenerate n)] :
    M.obj (((default : (nerve C).nonDegenerate n).val : ComposableArrows C n).obj 0) ≅
      (nondegCategoryChainComplex M).X n where
  hom := ιNondegCategoryChainComplex M (default : (nerve C).nonDegenerate n).val
  inv := Cofan.IsColimit.desc (isColimitCofanNondegCategoryChainComplex M n)
    fun y ↦ eqToHom (by rw [Subsingleton.elim y default])
  hom_inv_id := (Cofan.IsColimit.fac (isColimitCofanNondegCategoryChainComplex M n)
    (fun y ↦ eqToHom (by rw [Subsingleton.elim y default])) default).trans (eqToHom_refl _ _)
  inv_hom_id := Cofan.IsColimit.hom_ext (isColimitCofanNondegCategoryChainComplex M n) _ _
    fun y ↦ by
      obtain rfl : y = default := Subsingleton.elim _ _
      rw [← Category.assoc, Cofan.IsColimit.fac]; simp

@[simp] lemma nondegCategoryChainComplexXIsoOfUnique_hom (M : C ⥤ A) (n : ℕ)
    [Unique ((nerve C).nonDegenerate n)] :
    (nondegCategoryChainComplexXIsoOfUnique M n).hom =
      ιNondegCategoryChainComplex M (default : (nerve C).nonDegenerate n).val := by rfl

@[reassoc (attr := simp)]
lemma ιNondegCategoryChainComplex_nondegCategoryChainComplexXIsoOfUnique_inv (M : C ⥤ A)
    (n : ℕ) [Unique ((nerve C).nonDegenerate n)] (y : (nerve C).nonDegenerate n) :
    ιNondegCategoryChainComplex M y.val ≫ (nondegCategoryChainComplexXIsoOfUnique M n).inv =
      eqToHom (by rw [Subsingleton.elim y default]) := by
  exact Cofan.IsColimit.fac (isColimitCofanNondegCategoryChainComplex M n) _ y

section Homology

variable [CategoryWithHomology A]

instance quasiIso_toNondegCategoryChainComplex (M : C ⥤ A) :
    QuasiIso (toNondegCategoryChainComplex M) :=
  (homotopyEquivNondegCategoryChainComplex M).quasiIso_hom

instance quasiIso_fromNondegCategoryChainComplex (M : C ⥤ A) :
    QuasiIso (fromNondegCategoryChainComplex M) :=
  (homotopyEquivNondegCategoryChainComplex M).quasiIso_inv

/-- Canonical isomorphism `categoryHomology M n ≅` degree-`n` homology of
`nondegCategoryChainComplex M`. -/
def nondegCategoryHomologyIso (M : C ⥤ A) (n : ℕ) :
    categoryHomology M n ≅ (nondegCategoryChainComplex M).homology n :=
  (homotopyEquivNondegCategoryChainComplex M).toHomologyIso n

@[simp] lemma nondegCategoryHomologyIso_hom (M : C ⥤ A) (n : ℕ) :
    (nondegCategoryHomologyIso M n).hom =
      HomologicalComplex.homologyMap (toNondegCategoryChainComplex M) n := (rfl)

@[simp] lemma nondegCategoryHomologyIso_inv (M : C ⥤ A) (n : ℕ) :
    (nondegCategoryHomologyIso M n).inv =
      HomologicalComplex.homologyMap (fromNondegCategoryChainComplex M) n := (rfl)

end Homology

end Nondeg

/-- When `B` is abelian, `nondegCategoryChainComplex M` is canonically isomorphic to the Dold–Kan
normalized complex `normalizedCategoryChainComplex M`, the normalized Moore complex of
`categorySimplicialObject M`. -/
def nondegCategoryChainComplexIsoNormalized {C : Type u} [Category.{v} C]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasCoproducts.{max u v} B] (M : C ⥤ B) :
    nondegCategoryChainComplex M ≅ normalizedCategoryChainComplex M :=
  (Idempotents.fullyFaithfulToKaroubi (ChainComplex B ℕ)).preimageIso
    ((categorySimplicialObjectSplitting M).toKaroubiNondegComplexIsoN₁ ≪≫
      (N₁_iso_normalizedMooreComplex_comp_toKaroubi B).app (categorySimplicialObject M))

end TauCeti
