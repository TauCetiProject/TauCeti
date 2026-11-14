/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic

/-!
# Normalized chain complex for homology of a category with functor coefficients

For a category `C` and a functor `M : C ⥤ A` into a category `A` with coproducts, the simplicial
object `categorySimplicialObject C M` admits a canonical splitting
`categorySimplicialObjectSplitting C M` whose degree-`n` summand of nondegenerate simplices is
`∐_{σ ∈ (nerve C).nonDegenerate n} M(σ₀)`. Every epimorphism `φ : ⦋n⦌ ⟶ ⦋m⦌` in `SimplexCategory`
is surjective and monotone, hence fixes `0`, so `(categorySimplicialObject C M).map φ.op` acts as
the identity on `M(σ₀)` along the nerve's unique nondegenerate decomposition.

When `A` is preadditive, the associated nondegenerate complex `normalizedCategoryChainComplex C M`
is chain homotopy equivalent (hence quasi-isomorphic) to `categoryChainComplex C M`, vanishes on
degenerate nerve simplices, and (when `A` is abelian) is isomorphic to Dold-Kan's
`normalizedMooreComplex`.

## Main definitions

* `TauCeti.nerveNonDegSimplex`: underlying `ComposableArrows C n` of a nondegenerate `n`-simplex of
  `nerve C`.
* `TauCeti.categorySimplicialObjectSplitting`: canonical `SimplicialObject.Splitting` of
  `categorySimplicialObject C M` indexed by `(nerve C).nonDegenerate n`.
* `TauCeti.normalizedCategoryChainComplex`: normalized chain complex with degree-`n` chains
  `∐_{σ ∈ (nerve C).nonDegenerate n} M(σ₀)`.
* `TauCeti.toNormalizedCategoryChainComplex`, `TauCeti.fromNormalizedCategoryChainComplex`,
  `TauCeti.homotopyEquivNormalizedCategoryChainComplex`: retraction, section, and chain homotopy
  equivalence between `categoryChainComplex C M` and `normalizedCategoryChainComplex C M`.
* `TauCeti.ιNormalizedCategoryChainComplex`: generator map `M(σ₀) ⟶` degree-`n` normalized chains,
  vanishing on degenerate nerve simplices (`ιNormalizedCategoryChainComplex_eq_zero`).
* `TauCeti.normalizedCategoryHomologyIso`: canonical homology isomorphism
  `categoryHomology C M n ≅ (normalizedCategoryChainComplex C M).homology n`.
* `TauCeti.normalizedCategoryChainComplexIsoMoore`: isomorphism with Dold-Kan's
  `(normalizedMooreComplex B).obj (categorySimplicialObject C M)` when `B` is abelian.

## References

* [Daniel Quillen, *Higher algebraic K-theory: I*][quillen1973]
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
-/

public noncomputable section

universe v v' u u'

open CategoryTheory Limits Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial

namespace TauCeti

section Splitting

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]

/-- Underlying chain of `n` composable arrows of a nondegenerate `n`-simplex of `nerve C`. -/
def nerveNonDegSimplex {n : ℕ} (y : (nerve C).nonDegenerate n) : ComposableArrows C n :=
  y.1

@[simp]
lemma nerveNonDegSimplex_mk {n : ℕ} (σ : ComposableArrows C n)
    (hσ : (σ : (nerve C) _⦋n⦌) ∈ (nerve C).nonDegenerate n) :
    nerveNonDegSimplex ⟨σ, hσ⟩ = σ := (rfl)

private lemma toOrderHom_zero_of_epi {Δ Δ' : SimplexCategory} (α : Δ ⟶ Δ') [Epi α] :
    α.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (SimplexCategory.epi_iff_surjective.mp ‹Epi α›) 0
  exact le_antisymm (hk ▸ α.toOrderHom.monotone (Fin.zero_le k)) (Fin.zero_le _)

private lemma eqToHom_trans_inj {S : Type*} {Q : S → A} {T : A} (inj : ∀ s, Q s ⟶ T)
    {s s' : S} (hs : s' = s) {X : A} (h₁ : Q s = X) (h₂ : X = Q s') :
    eqToHom h₁ ≫ eqToHom h₂ ≫ inj s' = inj s := by
  subst hs
  simp

private def isColimitCofanOfEquiv {S : Type*} {J : Type*} (e : S ≃ J) {Q : S → A} {P : J → A}
    (cP : Cofan P) (hcP : IsColimit cP) (h : ∀ s, Q s = P (e s)) :
    IsColimit (Cofan.mk cP.pt (fun s ↦ eqToHom (h s) ≫ cP.inj (e s))) := by
  have hQ : ∀ j : J, P j = Q (e.symm j) := fun j ↦
    (congrArg P (e.apply_symm_apply j).symm).trans (h (e.symm j)).symm
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hcP fun j ↦ eqToHom (hQ j) ≫ t.inj (e.symm j))
    (fun t s ↦ ?_) (fun t m hm ↦ ?_)
  · dsimp only [Cofan.mk_pt, Limits.cofan_mk_inj]
    rw [Category.assoc, Cofan.IsColimit.fac]
    exact eqToHom_trans_inj t.inj (e.symm_apply_apply s) (h s) (hQ (e s))
  · refine Cofan.IsColimit.hom_ext hcP _ _ fun j ↦ ?_
    rw [Cofan.IsColimit.fac, ← hm (e.symm j)]
    dsimp only [Limits.cofan_mk_inj]
    rw [← Category.assoc]
    exact congrArg (· ≫ m)
      (eqToHom_trans_inj cP.inj (e.apply_symm_apply j) (hQ j) (h (e.symm j))).symm

private def isColimitCofanOfSigma {I : Type*} {β : I → Type*} {X : I → A} (c : Cofan X)
    {Y : ∀ i, β i → A} (π : ∀ i b, Y i b ⟶ X i)
    (hs : ∀ i, IsColimit (Cofan.mk (X i) (π i)))
    (htot : IsColimit (Cofan.mk (f := fun p : Σ i, β i ↦ Y p.1 p.2) c.pt
      (fun p ↦ π p.1 p.2 ≫ c.inj p.1))) :
    IsColimit c :=
  Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc htot fun p : Σ i, β i ↦ π p.1 p.2 ≫ t.inj p.1)
    (fun t i ↦ Cofan.IsColimit.hom_ext (hs i) _ _ fun b ↦ by
      dsimp only [Limits.cofan_mk_inj]
      rw [← Category.assoc]
      exact Cofan.IsColimit.fac htot (fun p : Σ i, β i ↦ π p.1 p.2 ≫ t.inj p.1) ⟨i, b⟩)
    (fun t m hm ↦ Cofan.IsColimit.hom_ext htot _ _ fun ⟨i, b⟩ ↦ by
      dsimp only [Cofan.mk_pt, Limits.cofan_mk_inj]
      rw [Category.assoc, hm]
      exact (Cofan.IsColimit.fac htot
        (fun p : Σ i, β i ↦ π p.1 p.2 ≫ t.inj p.1) ⟨i, b⟩).symm)

private lemma comp_d_distribute [Preadditive A] {X Y Z W : A} (u : X ⟶ Y) (v : Y ⟶ Z)
    {m : ℕ} (w : Fin m → (X ⟶ Z)) (g : Z ⟶ W) :
    (u ≫ v + ∑ j : Fin m, (-1 : ℤ) ^ (j.val + 1) • w j) ≫ g =
      u ≫ (v ≫ g) + ∑ j : Fin m, (-1 : ℤ) ^ (j.val + 1) • (w j ≫ g) := by
  rw [Preadditive.add_comp, Category.assoc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]

variable [HasCoproducts.{max u v} A]

private lemma ιCategorySimplicialObject_map_of_epi {m n : ℕ} (M : C ⥤ A) (φ : ⦋n⦌ ⟶ ⦋m⦌)
    [Epi φ] (σ : ComposableArrows C m) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).map φ.op =
      eqToHom (by
        change M.obj (σ.obj 0) = M.obj (σ.obj (φ.toOrderHom 0))
        rw [toOrderHom_zero_of_epi φ]) ≫
        ιCategorySimplicialObject M ((nerve C).map φ.op σ) := by
  rw [ιCategorySimplicialObject_map]
  refine congrArg (· ≫ _) (eq_of_heq ?_)
  have hz : φ.toOrderHom 0 = 0 := toOrderHom_zero_of_epi φ
  have hm : M.map (σ.map (homOfLE (Fin.zero_le (φ.toOrderHom 0)))) ≍ 𝟙 (M.obj (σ.obj 0)) := by
    generalize φ.toOrderHom 0 = z at hz ⊢
    subst hz
    have hid : homOfLE (Fin.zero_le (0 : Fin (m + 1))) = 𝟙 0 := Subsingleton.elim _ _
    rw [hid, σ.map_id, M.map_id]
  exact hm.trans (eqToHom_heq_id_dom _ _ _).symm

variable (C) in
/-- Canonical `SimplicialObject.Splitting` of `categorySimplicialObject C M` whose degree-`n`
summand of nondegenerate simplices is `∐_{y ∈ (nerve C).nonDegenerate n} M(y₀)`. -/
def categorySimplicialObjectSplitting (M : C ⥤ A) :
    (categorySimplicialObject C M).Splitting where
  N n := ∐ fun y : (nerve C).nonDegenerate n ↦ M.obj ((nerveNonDegSimplex y).obj 0)
  ι n := Sigma.desc fun y ↦ ιCategorySimplicialObject M (nerveNonDegSimplex y)
  isColimit' := fun ⟨⟨n⟩⟩ ↦ by
    let e : (Σ I : SimplicialObject.Splitting.IndexSet (op ⦋n⦌),
        (nerve C).nonDegenerate I.1.unop.len) ≃ ComposableArrows C n :=
      CofanTypes.equivOfIsColimit
        (((nerve C).splitting.cofan (op ⦋n⦌)).isColimit_cofanTypes_iff.mpr
          ⟨(nerve C).splitting.isColimit (op ⦋n⦌)⟩)
    have hEq : ∀ p : Σ I : SimplicialObject.Splitting.IndexSet (op ⦋n⦌),
        (nerve C).nonDegenerate I.1.unop.len,
        M.obj ((nerveNonDegSimplex p.2).obj 0) =
          M.obj ((e p).obj 0) := fun ⟨I, y⟩ ↦ by
      change M.obj ((nerveNonDegSimplex y).obj 0) =
        M.obj ((nerveNonDegSimplex y).obj (I.e.toOrderHom 0))
      rw [toOrderHom_zero_of_epi I.e]
    refine isColimitCofanOfSigma _
      (fun I y ↦ Sigma.ι (fun z : (nerve C).nonDegenerate I.1.unop.len ↦
        M.obj ((nerveNonDegSimplex z).obj 0)) y)
      (fun I ↦ coproductIsCoproduct _) ?_
    refine IsColimit.ofIsoColimit
      (isColimitCofanOfEquiv e (categorySimplicialObjectXCofan M n)
        (isColimitCategorySimplicialObjectXCofan M n) hEq)
      (Cofan.ext (Iso.refl _) ?_)
    rintro ⟨I, y⟩
    dsimp only [Cofan.mk_pt, Limits.cofan_mk_inj, SimplicialObject.Splitting.cofan', Iso.refl_hom]
    refine (Category.comp_id _).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (categorySimplicialObject C M).map I.e.op)
        (Sigma.ι_comp_desc (fun z : (nerve C).nonDegenerate I.1.unop.len ↦
          ιCategorySimplicialObject M (nerveNonDegSimplex z)) y)).trans
        (ιCategorySimplicialObject_map_of_epi M I.e (nerveNonDegSimplex y)))).symm

end Splitting

section Normalized

variable (C : Type u) [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

/-- The normalized chain complex computing homology of `C` with coefficients in `M : C ⥤ A`, with
degree-`n` object `∐_{σ ∈ (nerve C).nonDegenerate n} M(σ₀)`. -/
def normalizedCategoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (categorySimplicialObjectSplitting C M).nondegComplex

/-- The split epimorphism `categoryChainComplex C M ⟶ normalizedCategoryChainComplex C M`. -/
def toNormalizedCategoryChainComplex (M : C ⥤ A) :
    categoryChainComplex C M ⟶ normalizedCategoryChainComplex C M :=
  (categorySimplicialObjectSplitting C M).toNondegComplex

/-- The split monomorphism `normalizedCategoryChainComplex C M ⟶ categoryChainComplex C M`. -/
def fromNormalizedCategoryChainComplex (M : C ⥤ A) :
    normalizedCategoryChainComplex C M ⟶ categoryChainComplex C M :=
  (categorySimplicialObjectSplitting C M).fromNondegComplex

/-- Chain homotopy equivalence between `categoryChainComplex C M` and
`normalizedCategoryChainComplex C M`. -/
def homotopyEquivNormalizedCategoryChainComplex (M : C ⥤ A) :
    HomotopyEquiv (categoryChainComplex C M) (normalizedCategoryChainComplex C M) :=
  (categorySimplicialObjectSplitting C M).homotopyEquivNondegComplex

variable {C}

@[reassoc (attr := simp)]
lemma PInfty_toNormalizedCategoryChainComplex (M : C ⥤ A) :
    PInfty ≫ toNormalizedCategoryChainComplex C M = toNormalizedCategoryChainComplex C M :=
  SimplicialObject.Splitting.PInfty_toNondegComplex _

instance isSplitEpi_toNormalizedCategoryChainComplex (M : C ⥤ A) :
    IsSplitEpi (toNormalizedCategoryChainComplex C M) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

instance isSplitMono_fromNormalizedCategoryChainComplex (M : C ⥤ A) :
    IsSplitMono (fromNormalizedCategoryChainComplex C M) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]
lemma fromNormalizedCategoryChainComplex_toNormalizedCategoryChainComplex (M : C ⥤ A) :
    fromNormalizedCategoryChainComplex C M ≫ toNormalizedCategoryChainComplex C M = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]
lemma fromNormalizedCategoryChainComplex_f_toNormalizedCategoryChainComplex_f
    (M : C ⥤ A) (n : ℕ) :
    (fromNormalizedCategoryChainComplex C M).f n ≫
      (toNormalizedCategoryChainComplex C M).f n = 𝟙 _ := by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
lemma toNormalizedCategoryChainComplex_fromNormalizedCategoryChainComplex (M : C ⥤ A) :
    toNormalizedCategoryChainComplex C M ≫ fromNormalizedCategoryChainComplex C M = PInfty :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]
lemma toNormalizedCategoryChainComplex_f_fromNormalizedCategoryChainComplex_f
    (M : C ⥤ A) (n : ℕ) :
    (toNormalizedCategoryChainComplex C M).f n ≫
      (fromNormalizedCategoryChainComplex C M).f n = PInfty.f n := by
  simp [← HomologicalComplex.comp_f]

@[simp]
lemma homotopyEquivNormalizedCategoryChainComplex_hom (M : C ⥤ A) :
    (homotopyEquivNormalizedCategoryChainComplex C M).hom =
      toNormalizedCategoryChainComplex C M := (rfl)

@[simp]
lemma homotopyEquivNormalizedCategoryChainComplex_inv (M : C ⥤ A) :
    (homotopyEquivNormalizedCategoryChainComplex C M).inv =
      fromNormalizedCategoryChainComplex C M := (rfl)

/-- Generator morphism `M.obj (σ.obj 0) ⟶ (normalizedCategoryChainComplex C M).X n` attached to an
`n`-simplex `σ` of `nerve C`. This vanishes when `σ` is degenerate. -/
def ιNormalizedCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (normalizedCategoryChainComplex C M).X n :=
  ιCategoryChainComplex M σ ≫ (toNormalizedCategoryChainComplex C M).f n

/-- Alternating face boundary formula in `normalizedCategoryChainComplex C M`. -/
@[reassoc]
lemma ιNormalizedCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιNormalizedCategoryChainComplex M σ ≫ (normalizedCategoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          ιNormalizedCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          ιNormalizedCategoryChainComplex M ((nerve C).δ j.succ σ) :=
  ((Category.assoc _ _ _).trans
    (congrArg (ιCategoryChainComplex M σ ≫ ·)
      ((toNormalizedCategoryChainComplex C M).comm (n + 1) n))).trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (toNormalizedCategoryChainComplex C M).f n)
        (ιCategoryChainComplex_d M σ))).trans
      (comp_d_distribute (A := A) _ _ _ _))

private lemma ιCategoryChainComplex_σ_PInfty (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (τ : ComposableArrows C n) :
    ιCategoryChainComplex M ((nerve C).σ i τ) ≫
      (PInfty : categoryChainComplex C M ⟶ categoryChainComplex C M).f (n + 1) = 0 :=
  (congrArg (· ≫ _) (ιCategorySimplicialObject_σ M i τ).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (ιCategorySimplicialObject M τ ≫ ·)
        (σ_comp_PInfty (categorySimplicialObject C M) i)).trans Limits.comp_zero))

/-- `ιNormalizedCategoryChainComplex M σ` vanishes whenever `σ` is a degenerate nerve simplex. -/
lemma ιNormalizedCategoryChainComplex_eq_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n)
    (hσ : σ ∈ (nerve C).degenerate n) :
    ιNormalizedCategoryChainComplex M σ = 0 := by
  dsimp only [ιNormalizedCategoryChainComplex]
  rw [← PInfty_toNormalizedCategoryChainComplex, HomologicalComplex.comp_f, ← Category.assoc]
  obtain _ | n := n
  · rw [SSet.degenerate_zero] at hσ
    exact hσ.elim
  · have hσ' : (σ : (nerve C) _⦋n + 1⦌) ∈ ⋃ i, Set.range ((nerve C).σ i) := by
      simpa only [SSet.degenerate_eq_iUnion_range_σ] using hσ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ'
    obtain ⟨τ, hτ⟩ := Set.mem_range.mp hi
    have hzero : ∀ x : (nerve C) _⦋n + 1⦌, (nerve C).σ i τ = x →
        ιCategoryChainComplex M x ≫
          (PInfty : categoryChainComplex C M ⟶ categoryChainComplex C M).f (n + 1) = 0 := by
      rintro _ rfl
      exact ιCategoryChainComplex_σ_PInfty M i τ
    rw [hzero σ hτ, zero_comp]

private lemma ιNormalizedCategoryChainComplex_eq_ι (M : C ⥤ A) {n : ℕ}
    (y : (nerve C).nonDegenerate n) :
    ιNormalizedCategoryChainComplex M (nerveNonDegSimplex y) =
      Sigma.ι (fun z : (nerve C).nonDegenerate n ↦
        M.obj ((nerveNonDegSimplex z).obj 0)) y := by
  let s := categorySimplicialObjectSplitting C M
  have hP : PInfty.f n ≫ s.toNondegComplex.f n = s.toNondegComplex.f n := by
    rw [← HomologicalComplex.comp_f, s.PInfty_toNondegComplex]
  have hId : s.fromNondegComplex.f n ≫ s.toNondegComplex.f n = 𝟙 (s.nondegComplex.X n) := by
    rw [← HomologicalComplex.comp_f, s.fromNondegComplex_toNondegComplex,
      HomologicalComplex.id_f]
  have hs : s.ι n ≫ s.toNondegComplex.f n = 𝟙 (s.N n) :=
    (congrArg (s.ι n ≫ ·) hP.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s.toNondegComplex.f n) (s.fromNondegComplex_f n).symm).trans hId))
  have hcomp := congrArg
    (Sigma.ι (fun z : (nerve C).nonDegenerate n ↦
      M.obj ((nerveNonDegSimplex z).obj 0)) y ≫ ·) hs
  exact ((congrArg (· ≫ s.toNondegComplex.f n)
    (Sigma.ι_comp_desc (fun z : (nerve C).nonDegenerate n ↦
      ιCategorySimplicialObject M (nerveNonDegSimplex z)) y)).symm.trans
    ((Category.assoc _ _ _).trans (hcomp.trans (Category.comp_id _))))

/-- Cofan presenting `(normalizedCategoryChainComplex C M).X n` as the coproduct of `M(σ₀)` over
nondegenerate `n`-simplices `σ ∈ (nerve C).nonDegenerate n`. -/
abbrev cofanNormalizedCategoryChainComplex (M : C ⥤ A) (n : ℕ) :
    Cofan (fun y : (nerve C).nonDegenerate n ↦ M.obj ((nerveNonDegSimplex y).obj 0)) :=
  Cofan.mk ((normalizedCategoryChainComplex C M).X n)
    (fun y ↦ ιNormalizedCategoryChainComplex M (nerveNonDegSimplex y))

/-- `cofanNormalizedCategoryChainComplex M n` is a coproduct colimit. -/
def isColimitCofanNormalizedCategoryChainComplex (M : C ⥤ A) (n : ℕ) :
    IsColimit (cofanNormalizedCategoryChainComplex M n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) fun y ↦
      (Category.comp_id _).trans (ιNormalizedCategoryChainComplex_eq_ι M y).symm)

/-- Morphisms out of `(normalizedCategoryChainComplex C M).X n` are determined on nondegenerate
`n`-simplices of `nerve C`. -/
@[ext]
lemma normalizedCategoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (normalizedCategoryChainComplex C M).X n ⟶ T}
    (h : ∀ (σ : ComposableArrows C n), σ ∈ (nerve C).nonDegenerate n →
      ιNormalizedCategoryChainComplex M σ ≫ f = ιNormalizedCategoryChainComplex M σ ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (isColimitCofanNormalizedCategoryChainComplex M n) _ _
    fun ⟨σ, hσ⟩ ↦ h σ hσ

/-- When `(nerve C).nonDegenerate n` has a unique element `y`, the inclusion
`ιNormalizedCategoryChainComplex M (nerveNonDegSimplex y)` is an isomorphism onto degree-`n`
normalized chains. -/
def normalizedCategoryChainComplexXIsoOfUnique (M : C ⥤ A) (n : ℕ)
    [Unique ((nerve C).nonDegenerate n)] :
    M.obj ((nerveNonDegSimplex (default : (nerve C).nonDegenerate n)).obj 0) ≅
      (normalizedCategoryChainComplex C M).X n where
  hom := ιNormalizedCategoryChainComplex M (nerveNonDegSimplex default)
  inv := Cofan.IsColimit.desc (isColimitCofanNormalizedCategoryChainComplex M n)
    fun y ↦ eqToHom (by rw [Subsingleton.elim y default])
  hom_inv_id := by
    have hfac := Cofan.IsColimit.fac (isColimitCofanNormalizedCategoryChainComplex M n)
      (fun y : (nerve C).nonDegenerate n ↦
        eqToHom (by rw [Subsingleton.elim y default])) default
    simpa only [cofanNormalizedCategoryChainComplex, Limits.cofan_mk_inj, eqToHom_refl] using hfac
  inv_hom_id := by
    refine Cofan.IsColimit.hom_ext (isColimitCofanNormalizedCategoryChainComplex M n) _ _
      fun y ↦ ?_
    obtain rfl : y = default := Subsingleton.elim _ _
    have hfac := Cofan.IsColimit.fac (isColimitCofanNormalizedCategoryChainComplex M n)
      (fun z : (nerve C).nonDegenerate n ↦
        eqToHom (by rw [Subsingleton.elim z default])) default
    dsimp only [cofanNormalizedCategoryChainComplex, Limits.cofan_mk_inj] at hfac ⊢
    rw [← Category.assoc, hfac, eqToHom_refl, Category.id_comp]
    exact (Category.comp_id _).symm

@[simp]
lemma normalizedCategoryChainComplexXIsoOfUnique_hom (M : C ⥤ A) (n : ℕ)
    [Unique ((nerve C).nonDegenerate n)] :
    (normalizedCategoryChainComplexXIsoOfUnique M n).hom =
      ιNormalizedCategoryChainComplex M (nerveNonDegSimplex default) := (rfl)

section Homology

variable [CategoryWithHomology A]

instance quasiIso_toNormalizedCategoryChainComplex (M : C ⥤ A) :
    QuasiIso (toNormalizedCategoryChainComplex C M) :=
  (homotopyEquivNormalizedCategoryChainComplex C M).quasiIso_hom

instance quasiIso_fromNormalizedCategoryChainComplex (M : C ⥤ A) :
    QuasiIso (fromNormalizedCategoryChainComplex C M) :=
  (homotopyEquivNormalizedCategoryChainComplex C M).quasiIso_inv

/-- Canonical isomorphism between `categoryHomology C M n` and the degree-`n` homology of
`normalizedCategoryChainComplex C M`. -/
def normalizedCategoryHomologyIso (M : C ⥤ A) (n : ℕ) :
    categoryHomology C M n ≅ (normalizedCategoryChainComplex C M).homology n :=
  asIso (HomologicalComplex.homologyMap (toNormalizedCategoryChainComplex C M) n)

end Homology

end Normalized

/-- When `B` is abelian, `normalizedCategoryChainComplex C M` is canonically isomorphic to
Dold-Kan's `(normalizedMooreComplex B).obj (categorySimplicialObject C M)`. -/
def normalizedCategoryChainComplexIsoMoore {C : Type u} [Category.{v} C]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasCoproducts.{max u v} B] (M : C ⥤ B) :
    normalizedCategoryChainComplex C M ≅
      (normalizedMooreComplex B).obj (categorySimplicialObject C M) :=
  (Idempotents.fullyFaithfulToKaroubi (ChainComplex B ℕ)).preimageIso
    ((categorySimplicialObjectSplitting C M).toKaroubiNondegComplexIsoN₁ ≪≫
      (N₁_iso_normalizedMooreComplex_comp_toKaroubi B).app (categorySimplicialObject C M))

end TauCeti
