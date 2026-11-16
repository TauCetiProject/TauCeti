/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Colimit
public import TauCeti.Topology.Sheaves.Cech.Functoriality

/-!
# The cup product on Čech cohomology of a topological space

This file specializes the colimit Čech cup product of
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Colimit` to presheaves of `R`-modules on a
topological space `X : TopCat.{u}` (using point-neighborhood covers), packages the graded ring and
graded `R`-algebra structures arising from associative unital presheaf pairings, and proves
compatibility of the cup product and unit classes with pullback along continuous maps `f : X ⟶ Y`.

The graded Čech cohomology `R`-algebra with locally constant coefficients is constructed in
`TauCeti.Topology.Sheaves.Cech.Cup.Algebra`.

## Main definitions

* `TauCeti.Topology.cechCohomologyCup`: the `R`-bilinear cup product
  `Hᵖ(X, P) →ₗ[R] H^q(X, Q) →ₗ[R] Hⁿ(X, S)` induced by a natural `R`-bilinear pairing of presheaves
  on `X`.
* `TauCeti.Topology.cechCohomologyUnitClass`: the degree-`0` Čech cohomology class of a compatible
  family of sections.
* `TauCeti.Topology.cechCohomologyGRing`, `TauCeti.Topology.cechCohomologyGAlgebra`: the graded
  ring and graded `R`-algebra structures on `n ↦ Hⁿ(X, P)` for an associative unital presheaf
  pairing on `X`.

## Main results

* `TauCeti.Topology.cechCohomologyCup_toCechCohomology`: compatibility with `toCechCohomology` on
  every `u`-small open cover of `X`.
* `TauCeti.Topology.cechCohomologyCup_assoc`, `TauCeti.Topology.cechCohomologyCup_comm`,
  `TauCeti.Topology.cechCohomologyCup_naturality`: associativity, graded commutativity, and
  naturality in the coefficient presheaves.
* `TauCeti.Topology.cechCohomologyCup_finiteCechCohomologyIso_hom`: on a compact space, the
  identification with the colimit over finite open covers preserves the cup product.
* `TauCeti.Topology.cechCohomologyCup_cechCohomologyZeroIso_hom`: for sheaves,
  `cechCohomologyZeroIso` intertwines the global-sections pairing with the degree-`0` cup product.
* `TopCat.Hom.cechCohomologyPullback_cechCohomologyCup`,
  `TopCat.Hom.cechCohomologyPullback_cechCohomologyUnitClass`: pullback along a continuous map
  preserves the cup product and unit classes.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tags 01FP, 07MB), for the Čech cup product,
  its graded commutativity, and its compatibility with continuous maps.
* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY), for Čech cohomology as a colimit
  over open covers.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite DirectSum
open TauCeti.CategoryTheory

universe uR u

/-! ### Cup product on Čech cohomology of presheaves on a topological space -/

namespace TauCeti.Topology

section Presheaf

variable (X : TopCat.{u}) {R : Type uR} [CommRing R]
  {P Q S : X.Presheaf (ModuleCat.{u} R)}

/-- **The cup product on Čech cohomology of a topological space.** Given a natural `R`-bilinear
pairing `μ` of presheaves of `R`-modules on `X` and `p + q = n`, this is the unique `R`-bilinear
map `Hᵖ(X, P) →ₗ[R] H^q(X, Q) →ₗ[R] Hⁿ(X, S)` compatible with `cechComplexCup` on every `u`-small
open cover of `X` (`cechCohomologyCup_toCechCohomology`). -/
def cechCohomologyCup
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    (p q n : ℕ) (h : p + q = n) :
    (cechCohomology X (ModuleCat.{u} R) p).obj P →ₗ[R]
      (cechCohomology X (ModuleCat.{u} R) q).obj Q →ₗ[R]
        (cechCohomology X (ModuleCat.{u} R) n).obj S :=
  TauCeti.CategoryTheory.cechCohomologyCup PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    μ hμ p q n h

private lemma toCechCohomology_app_apply {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U)
    (V : PointOpenCover X) (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U)
    (P : X.Presheaf (ModuleCat.{u} R)) (n : ℕ)
    (x : ((cechComplexFunctor U).obj P).homology n) :
    (toCechCohomology (ModuleCat.{u} R) n U hU).app P x =
      (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V).app P
        (HomologicalComplex.homologyMap (cechComplexMap P φ) n x) := by
  have hm : ((toCechCohomology (ModuleCat.{u} R) n U hU).app P :
        ((cechComplexFunctor U).obj P).homology n ⟶
          (cechCohomology X (ModuleCat.{u} R) n).obj P) =
      HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V).app P :=
    (NatTrans.congr_app (toCechCohomology_eq (ModuleCat.{u} R) n U hU V φ) P).trans <|
      (NatTrans.comp_app (cechComplexHomologyMap (ModuleCat.{u} R) n φ)
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V) P).trans
        (cechComplexHomologyMap_app (ModuleCat.{u} R) n φ P =≫ _)
  exact (ConcreteCategory.congr_hom hm x).trans (ModuleCat.comp_apply _ _ x)

/-- On classes coming from any `u`-small open cover `U` of `X`, `cechCohomologyCup` agrees with
`cechComplexCup` on `Č(U, -)`. -/
theorem cechCohomologyCup_toCechCohomology
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    (p q n : ℕ) (h : p + q = n) {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    cechCohomologyCup X μ hμ p q n h
        ((toCechCohomology (ModuleCat.{u} R) p U hU).app P x)
        ((toCechCohomology (ModuleCat.{u} R) q U hU).app Q y) =
      (toCechCohomology (ModuleCat.{u} R) n U hU).app S
        (cechComplexCup U μ hμ p q n h x y) := by
  obtain ⟨V, ⟨φ⟩⟩ := PointOpenCover.exists_refinement U hU
  rw [toCechCohomology_app_apply X U hU V φ P p x,
    toCechCohomology_app_apply X U hU V φ Q q y,
    toCechCohomology_app_apply X U hU V φ S n _,
    cechCohomologyCup, cechCohomologyCup_ι, cechComplexCup_cechComplexMap]

/-- **Associativity of the Čech cup product on a topological space.** -/
theorem cechCohomologyCup_assoc {P₁ P₂ P₃ P₁₂ P₂₃ P₁₂₃ : X.Presheaf (ModuleCat.{u} R)}
    (μ₁₂ : ∀ U, P₁.obj U →ₗ[R] P₂.obj U →ₗ[R] P₁₂.obj U)
    (μ₁₂₃ : ∀ U, P₁₂.obj U →ₗ[R] P₃.obj U →ₗ[R] P₁₂₃.obj U)
    (μ₂₃ : ∀ U, P₂.obj U →ₗ[R] P₃.obj U →ₗ[R] P₂₃.obj U)
    (μ₁₂₃' : ∀ U, P₁.obj U →ₗ[R] P₂₃.obj U →ₗ[R] P₁₂₃.obj U)
    (hμ₁₂ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y,
      μ₁₂ V (P₁.map i x) (P₂.map i y) = P₁₂.map i (μ₁₂ U x y))
    (hμ₁₂₃ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y,
      μ₁₂₃ V (P₁₂.map i x) (P₃.map i y) = P₁₂₃.map i (μ₁₂₃ U x y))
    (hμ₂₃ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) y z,
      μ₂₃ V (P₂.map i y) (P₃.map i z) = P₂₃.map i (μ₂₃ U y z))
    (hμ₁₂₃' : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y,
      μ₁₂₃' V (P₁.map i x) (P₂₃.map i y) = P₁₂₃.map i (μ₁₂₃' U x y))
    (hassoc : ∀ U x y z, μ₁₂₃ U (μ₁₂ U x y) z = μ₁₂₃' U x (μ₂₃ U y z))
    (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n)
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj P₁)
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj P₂)
    (z : (cechCohomology X (ModuleCat.{u} R) r).obj P₃) :
    cechCohomologyCup X μ₁₂₃ hμ₁₂₃ pq r n hn
        (cechCohomologyCup X μ₁₂ hμ₁₂ p q pq hpq x y) z =
      cechCohomologyCup X μ₁₂₃' hμ₁₂₃' p qr n (by omega) x
        (cechCohomologyCup X μ₂₃ hμ₂₃ q r qr hqr y z) := by
  exact TauCeti.CategoryTheory.cechCohomologyCup_assoc PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' hμ₁₂ hμ₁₂₃ hμ₂₃ hμ₁₂₃' hassoc p q r pq qr n hpq hqr hn x y z

/-- **Graded commutativity of the Čech cup product on a topological space.** -/
theorem cechCohomologyCup_comm
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (μ' : ∀ U : (Opens X)ᵒᵖ, Q.obj U →ₗ[R] P.obj U →ₗ[R] S.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    (hμ' : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) y x,
      μ' V (Q.map i y) (P.map i x) = S.map i (μ' U y x))
    (hcomm : ∀ U x y, μ' U y x = μ U x y)
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj P)
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj Q) :
    cechCohomologyCup X μ' hμ' q p n (by omega) y x =
      (-1 : ℤ) ^ (p * q) • cechCohomologyCup X μ hμ p q n h x y := by
  exact TauCeti.CategoryTheory.cechCohomologyCup_comm PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) μ μ' hμ hμ' hcomm p q n h x y

/-- Naturality of the Čech cup product with respect to presheaf morphisms on `X`. -/
theorem cechCohomologyCup_naturality {P' Q' S' : X.Presheaf (ModuleCat.{u} R)}
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (μ' : ∀ U : (Opens X)ᵒᵖ, P'.obj U →ₗ[R] Q'.obj U →ₗ[R] S'.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    (hμ' : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y,
      μ' V (P'.map i x) (Q'.map i y) = S'.map i (μ' U x y))
    (α : P ⟶ P') (β : Q ⟶ Q') (γ : S ⟶ S')
    (hγ : ∀ U x y, γ.app U (μ U x y) = μ' U (α.app U x) (β.app U y))
    (p q n : ℕ) (h : p + q = n)
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj P)
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj Q) :
    (cechCohomology X (ModuleCat.{u} R) n).map γ (cechCohomologyCup X μ hμ p q n h x y) =
      cechCohomologyCup X μ' hμ' p q n h
        ((cechCohomology X (ModuleCat.{u} R) p).map α x)
        ((cechCohomology X (ModuleCat.{u} R) q).map β y) := by
  exact TauCeti.CategoryTheory.cechCohomologyCup_naturality PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) μ μ' hμ hμ' α β γ hγ p q n h x y

private lemma finiteCechCohomologyIso_hom_app_ι [CompactSpace X]
    (P : X.Presheaf (ModuleCat.{u} R)) (n : ℕ) (W : FiniteOpenCover X)
    (x : ((cechComplexFunctor W.opens).obj P).homology n) :
    (finiteCechCohomologyIso X (ModuleCat.{u} R) n).hom.app P
        ((cechCohomologyι FiniteOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n W).app P x) =
      (toCechCohomology (ModuleCat.{u} R) n W.opens W.isOpenCover).app P x := by
  have hm := NatTrans.congr_app
    (cechCohomologyι_comp_finiteCechCohomologyIso_hom X (ModuleCat.{u} R) n W) P
  exact (ModuleCat.comp_apply _ _ x).symm.trans (ConcreteCategory.congr_hom hm x)

/-- On a compact space, `finiteCechCohomologyIso` identifies the cup product computed over finite
open covers with `cechCohomologyCup`. -/
theorem cechCohomologyCup_finiteCechCohomologyIso_hom [CompactSpace X]
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    (p q n : ℕ) (h : p + q = n)
    (x : (TauCeti.CategoryTheory.cechCohomology (ModuleCat.{u} R)
      (FiniteOpenCover.toFormalCoproduct (X := X)) (fun _ _ h ↦ h) p).obj P)
    (y : (TauCeti.CategoryTheory.cechCohomology (ModuleCat.{u} R)
      (FiniteOpenCover.toFormalCoproduct (X := X)) (fun _ _ h ↦ h) q).obj Q) :
    (finiteCechCohomologyIso X (ModuleCat.{u} R) n).hom.app S
        (TauCeti.CategoryTheory.cechCohomologyCup FiniteOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
          μ hμ p q n h x y) =
      cechCohomologyCup X μ hμ p q n h
        ((finiteCechCohomologyIso X (ModuleCat.{u} R) p).hom.app P x)
        ((finiteCechCohomologyIso X (ModuleCat.{u} R) q).hom.app Q y) := by
  have hΦΨ : (TauCeti.CategoryTheory.cechCohomologyCup FiniteOpenCover.toFormalCoproduct
        (fun _ _ h ↦ h) μ hμ p q n h).compr₂
        ((finiteCechCohomologyIso X (ModuleCat.{u} R) n).hom.app S).hom =
      (cechCohomologyCup X μ hμ p q n h).compl₁₂
        ((finiteCechCohomologyIso X (ModuleCat.{u} R) p).hom.app P).hom
        ((finiteCechCohomologyIso X (ModuleCat.{u} R) q).hom.app Q).hom :=
    cechCohomology_bilinear_ext (R := R) (FiniteOpenCover.toFormalCoproduct (X := X))
      (fun _ _ h ↦ h) fun W a b ↦ by
      -- Unfold `LinearMap.compr₂`/`compl₁₂` and bundled `.hom` applications.
      change (finiteCechCohomologyIso X (ModuleCat.{u} R) n).hom.app S
          (TauCeti.CategoryTheory.cechCohomologyCup (FiniteOpenCover.toFormalCoproduct (X := X))
            (fun _ _ h ↦ h) μ hμ p q n h
            ((cechCohomologyι (FiniteOpenCover.toFormalCoproduct (X := X))
              (fun _ _ h ↦ h) p W).app P a)
            ((cechCohomologyι (FiniteOpenCover.toFormalCoproduct (X := X))
              (fun _ _ h ↦ h) q W).app Q b)) =
        cechCohomologyCup X μ hμ p q n h
          ((finiteCechCohomologyIso X (ModuleCat.{u} R) p).hom.app P
            ((cechCohomologyι (FiniteOpenCover.toFormalCoproduct (X := X))
              (fun _ _ h ↦ h) p W).app P a))
          ((finiteCechCohomologyIso X (ModuleCat.{u} R) q).hom.app Q
            ((cechCohomologyι (FiniteOpenCover.toFormalCoproduct (X := X))
              (fun _ _ h ↦ h) q W).app Q b))
      rw [cechCohomologyCup_ι, finiteCechCohomologyIso_hom_app_ι,
        finiteCechCohomologyIso_hom_app_ι, finiteCechCohomologyIso_hom_app_ι,
        cechCohomologyCup_toCechCohomology]
  exact congrArg (fun f ↦ f x y) hΦΨ

/-- The degree-`0` Čech cohomology class on `X` of a compatible family of sections `e`. -/
def cechCohomologyUnitClass (P : X.Presheaf (ModuleCat.{u} R)) (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V) :
    (cechCohomology X (ModuleCat.{u} R) 0).obj P :=
  TauCeti.CategoryTheory.cechCohomologyUnitClass PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    P e he

/-- `cechCohomologyUnitClass` is the image of `cechUnitClass` from any `u`-small open cover `U`. -/
theorem cechCohomologyUnitClass_eq_toCechCohomology (P : X.Presheaf (ModuleCat.{u} R))
    (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V)
    {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    cechCohomologyUnitClass X P e he =
      (toCechCohomology (ModuleCat.{u} R) 0 U hU).app P (cechUnitClass U P e he) := by
  obtain ⟨V, ⟨φ⟩⟩ := PointOpenCover.exists_refinement U hU
  rw [toCechCohomology_app_apply X U hU V φ P 0, homologyMap_cechComplexMap_cechUnitClass,
    cechCohomologyUnitClass, cechCohomologyUnitClass_eq_ι]

/-- Left unit law for `cechCohomologyCup`. -/
theorem cechCohomologyCup_unit_left
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] Q.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = Q.map i (μ U x y))
    (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V)
    (hl : ∀ U y, μ U (e U) y = y) (q : ℕ)
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj Q) :
    cechCohomologyCup X μ hμ 0 q q (zero_add q) (cechCohomologyUnitClass X P e he) y = y := by
  exact TauCeti.CategoryTheory.cechCohomologyCup_unit_left PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) μ hμ e he hl q y

/-- Right unit law for `cechCohomologyCup`. -/
theorem cechCohomologyCup_unit_right
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] P.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = P.map i (μ U x y))
    (e : ∀ U : (Opens X)ᵒᵖ, Q.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Q.map i (e U) = e V)
    (hr : ∀ U x, μ U x (e U) = x) (p : ℕ)
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj P) :
    cechCohomologyCup X μ hμ p 0 p (add_zero p) x (cechCohomologyUnitClass X Q e he) = x := by
  exact TauCeti.CategoryTheory.cechCohomologyCup_unit_right PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) μ hμ e he hr p x

/-- Morphisms of presheaves preserving compatible unit sections preserve
`cechCohomologyUnitClass`. -/
theorem cechCohomology_map_cechCohomologyUnitClass (α : P ⟶ Q)
    (eP : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (heP : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (eP U) = eP V)
    (eQ : ∀ U : (Opens X)ᵒᵖ, Q.obj U)
    (heQ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Q.map i (eQ U) = eQ V)
    (hα : ∀ U, α.app U (eP U) = eQ U) :
    (cechCohomology X (ModuleCat.{u} R) 0).map α (cechCohomologyUnitClass X P eP heP) =
      cechCohomologyUnitClass X Q eQ heQ := by
  exact TauCeti.CategoryTheory.cechCohomology_map_cechCohomologyUnitClass
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) α eP heP eQ heQ hα

/-- On a compact space, `finiteCechCohomologyIso` preserves `cechCohomologyUnitClass`. -/
theorem cechCohomologyUnitClass_finiteCechCohomologyIso_hom [CompactSpace X]
    (P : X.Presheaf (ModuleCat.{u} R)) (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V) :
    (finiteCechCohomologyIso X (ModuleCat.{u} R) 0).hom.app P
        (TauCeti.CategoryTheory.cechCohomologyUnitClass FiniteOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) P e he) =
      cechCohomologyUnitClass X P e he := by
  let W : FiniteOpenCover X := default
  rw [TauCeti.CategoryTheory.cechCohomologyUnitClass_eq_ι FiniteOpenCover.toFormalCoproduct
      (fun _ _ h ↦ h) P e he W,
    finiteCechCohomologyIso_hom_app_ι,
    ← cechCohomologyUnitClass_eq_toCechCohomology X P e he W.opens W.isOpenCover]

private lemma cechCohomologyZeroIso_hom_apply_cover
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (U : PointOpenCover X)
    (x : F.obj.obj (op ⊤)) :
    (cechCohomologyZeroIso F).hom x =
      (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 U).app F.obj
        (HomologicalComplex.homologyMap (cechAugmentation U.opens isTerminalTop F.obj) 0
          ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
            (F.obj.obj (op ⊤))).inv x)) := by
  have h := ConcreteCategory.congr_hom (cechCohomologyZeroIso_hom F U) x
  exact h.trans <| (ModuleCat.comp_apply _ _ x).trans (ModuleCat.comp_apply _ _ _)

/-- For a sheaf `F` on `X`, `cechCohomologyZeroIso` sends a global section `e₀ ∈ F(X)` to the
`cechCohomologyUnitClass` of its restrictions. -/
theorem cechCohomologyZeroIso_hom_eq_cechCohomologyUnitClass
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (e₀ : F.obj.obj (op ⊤)) :
    (cechCohomologyZeroIso F).hom e₀ =
      cechCohomologyUnitClass X F.obj (fun U ↦ F.obj.map (isTerminalTop.from U.unop).op e₀)
        (fun {U V} i ↦ by
          rw [← ModuleCat.comp_apply, ← F.obj.map_comp]
          have hcomp : (isTerminalTop.from U.unop).op ≫ i = (isTerminalTop.from V.unop).op :=
            Quiver.Hom.unop_inj (Subsingleton.elim _ _)
          rw [hcomp]) := by
  let U : PointOpenCover X := default
  rw [cechCohomologyZeroIso_hom_apply_cover X F U e₀, cechCohomologyUnitClass,
    cechCohomologyUnitClass_eq_ι _ _ _ _ _ U,
    cechUnitClass_eq_homologyMap_cechAugmentation U.opens isTerminalTop F.obj e₀]

/-- For sheaves `F`, `G`, `H` on `X`, `cechCohomologyZeroIso` intertwines the global-sections
pairing with the degree-`0` cup product. -/
theorem cechCohomologyCup_cechCohomologyZeroIso_hom
    (F G H : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (μ : ∀ U : (Opens X)ᵒᵖ, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y,
      μ V (F.obj.map i x) (G.obj.map i y) = H.obj.map i (μ U x y))
    (x : F.obj.obj (op ⊤)) (y : G.obj.obj (op ⊤)) :
    cechCohomologyCup X μ hμ 0 0 0 rfl
        ((cechCohomologyZeroIso F).hom x) ((cechCohomologyZeroIso G).hom y) =
      (cechCohomologyZeroIso H).hom (μ (op ⊤) x y) := by
  let U : PointOpenCover X := default
  rw [cechCohomologyZeroIso_hom_apply_cover X F U x,
    cechCohomologyZeroIso_hom_apply_cover X G U y,
    cechCohomologyZeroIso_hom_apply_cover X H U _,
    cechCohomologyCup, cechCohomologyCup_ι,
    cechComplexCup_homologyMap_cechAugmentation U.opens isTerminalTop μ hμ x y]

/-! ### Graded ring and algebra structures for associative unital presheaf pairings -/

/-- Changing the proof of `p + q = n` in `cechCohomologyCup` yields a heterogeneously equal
element. -/
theorem cechCohomologyCup_heq
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] S.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (Q.map i y) = S.map i (μ U x y))
    {p q n₁ n₂ : ℕ} (h₁ : p + q = n₁) (h₂ : p + q = n₂)
    (x : (cechCohomology X (ModuleCat.{u} R) p).obj P)
    (y : (cechCohomology X (ModuleCat.{u} R) q).obj Q) :
    HEq (cechCohomologyCup X μ hμ p q n₁ h₁ x y) (cechCohomologyCup X μ hμ p q n₂ h₂ x y) := by
  subst h₁
  subst h₂
  rfl

/-- **The graded Čech cohomology ring of an associative unital presheaf pairing.** Given a presheaf
`P` of `R`-modules on `X` with an associative natural `R`-bilinear multiplication `μ` and a
compatible two-sided unit `e`, the cup product equips `n ↦ Hⁿ(X, P)` with a `DirectSum.GRing`
structure.

This is not an instance because `μ` and `e` do not appear in its type; it is reducible so that
instances defined from it unfold cleanly. -/
abbrev cechCohomologyGRing (P : X.Presheaf (ModuleCat.{u} R))
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] P.obj U →ₗ[R] P.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (P.map i y) = P.map i (μ U x y))
    (hassoc : ∀ U x y z, μ U (μ U x y) z = μ U x (μ U y z))
    (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V)
    (hl : ∀ U x, μ U (e U) x = x) (hr : ∀ U x, μ U x (e U) = x) :
    DirectSum.GRing fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj P : Type u) :=
  letI : GradedMonoid.GMul fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj P : Type u) :=
    ⟨fun {p q} x y ↦ cechCohomologyCup X μ hμ p q (p + q) rfl x y⟩
  letI : GradedMonoid.GOne fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj P : Type u) :=
    ⟨cechCohomologyUnitClass X P e he⟩
  { one_mul := fun ⟨n, x⟩ ↦ Sigma.ext (Nat.zero_add n)
      ((cechCohomologyCup_heq X μ hμ rfl (Nat.zero_add n) _ x).trans
        (heq_of_eq (cechCohomologyCup_unit_left X μ hμ e he hl n x)))
    mul_one := fun ⟨n, x⟩ ↦ Sigma.ext (Nat.add_zero n)
      (heq_of_eq (cechCohomologyCup_unit_right X μ hμ e he hr n x))
    mul_assoc := fun ⟨p, x⟩ ⟨q, y⟩ ⟨r, z⟩ ↦ Sigma.ext (Nat.add_assoc p q r)
      ((heq_of_eq (cechCohomologyCup_assoc X μ μ μ μ hμ hμ hμ hμ hassoc p q r (p + q) (q + r)
          ((p + q) + r) rfl rfl rfl x y z)).trans
        (cechCohomologyCup_heq X μ hμ (by omega) rfl x _))
    mul_zero x := (cechCohomologyCup X μ hμ _ _ _ rfl x).map_zero
    zero_mul y := LinearMap.congr_fun (map_zero (cechCohomologyCup X μ hμ _ _ _ rfl)) y
    mul_add x y z := (cechCohomologyCup X μ hμ _ _ _ rfl x).map_add y z
    add_mul x y z := LinearMap.congr_fun ((cechCohomologyCup X μ hμ _ _ _ rfl).map_add x y) z
    natCast n := n • cechCohomologyUnitClass X P e he
    natCast_zero := zero_nsmul _
    natCast_succ n := succ_nsmul _ n
    intCast n := n • cechCohomologyUnitClass X P e he
    intCast_ofNat n := natCast_zsmul _ n
    intCast_negSucc_ofNat n := negSucc_zsmul _ n }

/-- **The graded Čech cohomology `R`-algebra of an associative unital presheaf pairing.** -/
abbrev cechCohomologyGAlgebra (P : X.Presheaf (ModuleCat.{u} R))
    (μ : ∀ U : (Opens X)ᵒᵖ, P.obj U →ₗ[R] P.obj U →ₗ[R] P.obj U)
    (hμ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) x y, μ V (P.map i x) (P.map i y) = P.map i (μ U x y))
    (hassoc : ∀ U x y z, μ U (μ U x y) z = μ U x (μ U y z))
    (e : ∀ U : (Opens X)ᵒᵖ, P.obj U)
    (he : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), P.map i (e U) = e V)
    (hl : ∀ U x, μ U (e U) x = x) (hr : ∀ U x, μ U x (e U) = x) :
    letI := cechCohomologyGRing X P μ hμ hassoc e he hl hr
    DirectSum.GAlgebra R fun n : ℕ ↦ ((cechCohomology X (ModuleCat.{u} R) n).obj P : Type u) :=
  letI := cechCohomologyGRing X P μ hμ hassoc e he hl hr
  { toFun :=
      { toFun := fun r ↦ r • cechCohomologyUnitClass X P e he
        map_zero' := zero_smul R _
        map_add' := fun r s ↦ add_smul r s _ }
    map_one := one_smul R _
    map_mul := fun r s ↦ Sigma.ext (Nat.zero_add 0).symm <| heq_of_eq <| by
      -- Unfold `GradedMonoid.GMul.mul` to `cechCohomologyCup`.
      change (r * s) • cechCohomologyUnitClass X P e he =
        cechCohomologyCup X μ hμ 0 0 0 rfl
          (r • cechCohomologyUnitClass X P e he) (s • cechCohomologyUnitClass X P e he)
      rw [map_smul, map_smul, LinearMap.smul_apply,
        cechCohomologyCup_unit_left X μ hμ e he hl 0 _, smul_smul, mul_comm]
    commutes := fun r ⟨n, x⟩ ↦ Sigma.ext ((Nat.zero_add n).trans (Nat.add_zero n).symm) <| by
      -- Unfold `GradedMonoid.GMul.mul` to `cechCohomologyCup` and adjust degree `0 + n = n + 0`.
      change HEq
        (cechCohomologyCup X μ hμ 0 n (0 + n) rfl (r • cechCohomologyUnitClass X P e he) x)
        (cechCohomologyCup X μ hμ n 0 (n + 0) rfl x (r • cechCohomologyUnitClass X P e he))
      refine (cechCohomologyCup_heq X μ hμ rfl (Nat.zero_add n) _ x).trans <| heq_of_eq ?_
      change cechCohomologyCup X μ hμ 0 n n (zero_add n) (r • cechCohomologyUnitClass X P e he) x =
        cechCohomologyCup X μ hμ n 0 n (add_zero n) x (r • cechCohomologyUnitClass X P e he)
      rw [map_smul, LinearMap.smul_apply, cechCohomologyCup_unit_left X μ hμ e he hl n x,
        map_smul, cechCohomologyCup_unit_right X μ hμ e he hr n x]
    smul_def := fun r ⟨n, x⟩ ↦ Sigma.ext (Nat.zero_add n).symm <| by
      -- Unfold `GradedMonoid.GMul.mul` to `cechCohomologyCup` and rewrite via the left unit law.
      change HEq (r • x)
        (cechCohomologyCup X μ hμ 0 n (0 + n) rfl (r • cechCohomologyUnitClass X P e he) x)
      refine (heq_of_eq ?_).trans (cechCohomologyCup_heq X μ hμ (Nat.zero_add n) rfl _ x)
      rw [map_smul, LinearMap.smul_apply, cechCohomologyCup_unit_left X μ hμ e he hl n x] }

end Presheaf

end TauCeti.Topology

/-! ### Pullback compatibility along continuous maps -/

namespace TopCat.Hom

open TauCeti.Topology (PointOpenCover)

section Cup

variable {R : Type uR} [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y)

private lemma cechComplexπ_cechComplexPullback {ι : Type u} (U : ι → Opens Y)
    {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (n : ℕ) (c : Fin (n + 1) → ι) (a : ((cechComplexFunctor U).obj P).X n) :
    cechComplexπ (fun i ↦ (Opens.map f).obj (U i)) P' n c ((f.cechComplexPullback U α).f n a) =
      P'.map (inv (piComparison (Opens.map f) (fun j ↦ U (c j)))).op
        (α.app (op (∏ᶜ fun j ↦ U (c j))) (cechComplexπ U P n c a)) := by
  have hm : (f.cechComplexPullback U α).f n ≫
        cechComplexπ (fun i ↦ (Opens.map f).obj (U i)) P' n c =
      cechComplexπ U P n c ≫ α.app (op (∏ᶜ fun j ↦ U (c j))) ≫
        P'.map (inv (piComparison (Opens.map f) (fun j ↦ U (c j)))).op := by
    rw [cechComplexπ_eq, cechComplexπ_eq]
    exact f.cechComplexPullback_f_π U α n c
  exact (ModuleCat.comp_apply _ _ a).symm.trans <|
    (ConcreteCategory.congr_hom hm a).trans <|
      (ModuleCat.comp_apply _ _ a).trans (ModuleCat.comp_apply _ _ _)

private lemma presheaf_map_map' {F : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : F.obj U) :
    F.map j (F.map i x) = F.map (i ≫ j) x := by
  rw [F.map_comp, ModuleCat.comp_apply]

/-- Naturality of a coefficient pullback `α : P ⟶ f_* P'` with respect to finite-product face
projections and the inverse-image intersection isomorphism `piComparison`. -/
private lemma cechComplexPullback_face_restriction {ι : Type u} (U : ι → Opens Y)
    {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    {k n : ℕ} (c : Fin (n + 1) → ι) (g : Fin (k + 1) → Fin (n + 1))
    (a : P.obj (op (∏ᶜ fun j : Fin (k + 1) ↦ U (c (g j))))) :
    P'.map (inv (piComparison (Opens.map f) fun j ↦ U (c j))).op
        (α.app (op (∏ᶜ fun j ↦ U (c j)))
          (P.map (Limits.Pi.lift fun j : Fin (k + 1) ↦
            Limits.Pi.π (fun i : Fin (n + 1) ↦ U (c i)) (g j)).op a)) =
      P'.map (Limits.Pi.lift fun j : Fin (k + 1) ↦
          Limits.Pi.π (fun i : Fin (n + 1) ↦ (Opens.map f).obj (U (c i))) (g j)).op
        (P'.map (inv (piComparison (Opens.map f) fun j : Fin (k + 1) ↦ U (c (g j)))).op
          (α.app (op (∏ᶜ fun j : Fin (k + 1) ↦ U (c (g j)))) a)) := by
  have hα : α.app (op (∏ᶜ fun j ↦ U (c j)))
        (P.map (Limits.Pi.lift fun j : Fin (k + 1) ↦
          Limits.Pi.π (fun i : Fin (n + 1) ↦ U (c i)) (g j)).op a) =
      P'.map ((Opens.map f).map (Limits.Pi.lift fun j : Fin (k + 1) ↦
          Limits.Pi.π (fun i : Fin (n + 1) ↦ U (c i)) (g j))).op
        (α.app (op (∏ᶜ fun j : Fin (k + 1) ↦ U (c (g j)))) a) := by
    rw [← ModuleCat.comp_apply, α.naturality, ModuleCat.comp_apply]
    rfl
  have hsq : ((Opens.map f).map (Limits.Pi.lift fun j : Fin (k + 1) ↦
        Limits.Pi.π (fun i : Fin (n + 1) ↦ U (c i)) (g j))).op ≫
        (inv (piComparison (Opens.map f) fun j ↦ U (c j))).op =
      (inv (piComparison (Opens.map f) fun j : Fin (k + 1) ↦ U (c (g j)))).op ≫
        (Limits.Pi.lift fun j : Fin (k + 1) ↦
          Limits.Pi.π (fun i : Fin (n + 1) ↦ (Opens.map f).obj (U (c i))) (g j)).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hα, presheaf_map_map', presheaf_map_map', hsq]

/-- Pullback of Čech complexes along a continuous map commutes with the cochain cup product. -/
theorem cechComplexPullback_cechCupCochain {ι : Type u} (U : ι → Opens Y)
    {P Q S : Y.Presheaf (ModuleCat.{u} R)} {P' Q' S' : X.Presheaf (ModuleCat.{u} R)}
    (μ : ∀ V : (Opens Y)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (μ' : ∀ V : (Opens X)ᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) x y,
      μ' W (P'.map i x) (Q'.map i y) = S'.map i (μ' V x y))
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (β : Q ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj Q')
    (γ : S ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' (op ((Opens.map f).obj V.unop)) (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (a : ((cechComplexFunctor U).obj P).X p) (b : ((cechComplexFunctor U).obj Q).X q) :
    (f.cechComplexPullback U γ).f n (cechCupCochain U μ p q n h a b) =
      cechCupCochain (fun i ↦ (Opens.map f).obj (U i)) μ' p q n h
        ((f.cechComplexPullback U α).f p a) ((f.cechComplexPullback U β).f q b) := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechComplexπ_cechComplexPullback, cechCupCochain_π, cechCupCochain_π, hγ, ← hμ',
    cechComplexπ_cechComplexPullback, cechComplexπ_cechComplexPullback,
    cechComplexPullback_face_restriction f U α c (fun j : Fin (p + 1) ↦ ⟨j.val, by omega⟩),
    cechComplexPullback_face_restriction f U β c (fun j : Fin (q + 1) ↦ ⟨p + j.val, by omega⟩)]

/-- Pullback of fixed-cover Čech complexes commutes with `cechComplexCup` on cohomology. -/
theorem cechComplexPullback_cechComplexCup {ι : Type u} (U : ι → Opens Y)
    {P Q S : Y.Presheaf (ModuleCat.{u} R)} {P' Q' S' : X.Presheaf (ModuleCat.{u} R)}
    (μ : ∀ V : (Opens Y)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (μ' : ∀ V : (Opens X)ᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ : ∀ {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W) x y,
      μ W (P.map i x) (Q.map i y) = S.map i (μ V x y))
    (hμ' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) x y,
      μ' W (P'.map i x) (Q'.map i y) = S'.map i (μ' V x y))
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (β : Q ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj Q')
    (γ : S ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' (op ((Opens.map f).obj V.unop)) (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (x : ((cechComplexFunctor U).obj P).homology p)
    (y : ((cechComplexFunctor U).obj Q).homology q) :
    HomologicalComplex.homologyMap (f.cechComplexPullback U γ) n
        (cechComplexCup U μ hμ p q n h x y) =
      cechComplexCup (fun i ↦ (Opens.map f).obj (U i)) μ' hμ' p q n h
        (HomologicalComplex.homologyMap (f.cechComplexPullback U α) p x)
        (HomologicalComplex.homologyMap (f.cechComplexPullback U β) q y) :=
  homologyMap_cechComplexCup_of_f U μ μ' hμ hμ'
    (f.cechComplexPullback U α) (f.cechComplexPullback U β) (f.cechComplexPullback U γ)
    p q n h (f.cechComplexPullback_cechCupCochain U μ μ' hμ' α β γ hγ p q n h) x y

/-- Pullback of Čech complexes sends `cechUnitCochain` to `cechUnitCochain`. -/
theorem cechComplexPullback_cechUnitCochain {ι : Type u} (U : ι → Opens Y)
    {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (eP : ∀ V : (Opens Y)ᵒᵖ, P.obj V)
    (eP' : ∀ V : (Opens X)ᵒᵖ, P'.obj V)
    (heP' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W), P'.map i (eP' V) = eP' W)
    (hα : ∀ V, α.app V (eP V) = eP' (op ((Opens.map f).obj V.unop))) :
    (f.cechComplexPullback U α).f 0 (cechUnitCochain U P eP) =
      cechUnitCochain (fun i ↦ (Opens.map f).obj (U i)) P' eP' := by
  refine cechComplex_ext fun c ↦ ?_
  rw [cechComplexπ_cechComplexPullback, cechUnitCochain_π, cechUnitCochain_π, hα, heP']

/-- Pullback of fixed-cover Čech complexes preserves `cechUnitClass`. -/
theorem cechComplexPullback_cechUnitClass {ι : Type u} (U : ι → Opens Y)
    {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (eP : ∀ V : (Opens Y)ᵒᵖ, P.obj V)
    (heP : ∀ {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W), P.map i (eP V) = eP W)
    (eP' : ∀ V : (Opens X)ᵒᵖ, P'.obj V)
    (heP' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W), P'.map i (eP' V) = eP' W)
    (hα : ∀ V, α.app V (eP V) = eP' (op ((Opens.map f).obj V.unop))) :
    HomologicalComplex.homologyMap (f.cechComplexPullback U α) 0 (cechUnitClass U P eP heP) =
      cechUnitClass (fun i ↦ (Opens.map f).obj (U i)) P' eP' heP' :=
  homologyMap_cechUnitClass_of_f_zero U (f.cechComplexPullback U α) eP heP eP' heP'
    (f.cechComplexPullback_cechUnitCochain U α eP eP' heP' hα)

private lemma cechCohomologyPullback_toCechCohomology_apply {ι : Type u} (U : ι → Opens Y)
    (hU : IsOpenCover U) {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P') (n : ℕ)
    (x : ((cechComplexFunctor U).obj P).homology n) :
    f.cechCohomologyPullback n α
        ((TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) n U hU).app P x) =
      (TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) n
          (fun i ↦ (Opens.map f).obj (U i)) (hU.comap f.hom)).app P'
        (HomologicalComplex.homologyMap (f.cechComplexPullback U α) n x) := by
  have h : (((TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) n U hU).app P ≫
        f.cechCohomologyPullback n α) :
        ((cechComplexFunctor U).obj P).homology n ⟶
          (TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) n).obj P') x =
      ((HomologicalComplex.homologyMap (f.cechComplexPullback U α) n ≫
        (TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) n
          (fun i ↦ (Opens.map f).obj (U i)) (hU.comap f.hom)).app P') :
        ((cechComplexFunctor U).obj P).homology n ⟶
          (TauCeti.Topology.cechCohomology X (ModuleCat.{u} R) n).obj P') x :=
    ConcreteCategory.congr_hom (f.toCechCohomology_app_comp_cechCohomologyPullback n α U hU) x
  exact (ModuleCat.comp_apply _ _ x).symm.trans (h.trans (ModuleCat.comp_apply _ _ x))

/-- **Pullback along a continuous map commutes with the Čech cup product.** -/
theorem cechCohomologyPullback_cechCohomologyCup
    {P Q S : Y.Presheaf (ModuleCat.{u} R)} {P' Q' S' : X.Presheaf (ModuleCat.{u} R)}
    (μ : ∀ V : (Opens Y)ᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] S.obj V)
    (μ' : ∀ V : (Opens X)ᵒᵖ, P'.obj V →ₗ[R] Q'.obj V →ₗ[R] S'.obj V)
    (hμ : ∀ {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W) x y,
      μ W (P.map i x) (Q.map i y) = S.map i (μ V x y))
    (hμ' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) x y,
      μ' W (P'.map i x) (Q'.map i y) = S'.map i (μ' V x y))
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (β : Q ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj Q')
    (γ : S ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj S')
    (hγ : ∀ V x y, γ.app V (μ V x y) = μ' (op ((Opens.map f).obj V.unop)) (α.app V x) (β.app V y))
    (p q n : ℕ) (h : p + q = n)
    (x : (TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) p).obj P)
    (y : (TauCeti.Topology.cechCohomology Y (ModuleCat.{u} R) q).obj Q) :
    f.cechCohomologyPullback n γ (TauCeti.Topology.cechCohomologyCup Y μ hμ p q n h x y) =
      TauCeti.Topology.cechCohomologyCup X μ' hμ' p q n h
        (f.cechCohomologyPullback p α x) (f.cechCohomologyPullback q β y) := by
  have hΦΨ : (TauCeti.Topology.cechCohomologyCup Y μ hμ p q n h).compr₂
        (f.cechCohomologyPullback n γ).hom =
      (TauCeti.Topology.cechCohomologyCup X μ' hμ' p q n h).compl₁₂
        (f.cechCohomologyPullback p α).hom (f.cechCohomologyPullback q β).hom :=
    cechCohomology_bilinear_ext (R := R) (PointOpenCover.toFormalCoproduct (X := Y))
      (fun _ _ h ↦ h) fun U a b ↦ by
      -- Unfold `LinearMap.compr₂`/`compl₁₂` and bundled `.hom` applications.
      change f.cechCohomologyPullback n γ
          (TauCeti.Topology.cechCohomologyCup Y μ hμ p q n h
            ((cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
              (fun _ _ h ↦ h) p U).app P a)
            ((cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
              (fun _ _ h ↦ h) q U).app Q b)) =
        TauCeti.Topology.cechCohomologyCup X μ' hμ' p q n h
          (f.cechCohomologyPullback p α
            ((cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
              (fun _ _ h ↦ h) p U).app P a))
          (f.cechCohomologyPullback q β
            ((cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
              (fun _ _ h ↦ h) q U).app Q b))
      -- Rewrite the colimit insertions into `toCechCohomology` on `U.opens` and pull back.
      have hιp : (cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
            (fun _ _ h ↦ h) p U).app P a =
          (TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) p U.opens U.isOpenCover).app P a :=
        congrArg (fun t ↦ t.app P a)
          (TauCeti.Topology.toCechCohomology_opens (ModuleCat.{u} R) p U).symm
      have hιq : (cechCohomologyι (A := ModuleCat.{u} R) (PointOpenCover.toFormalCoproduct (X := Y))
            (fun _ _ h ↦ h) q U).app Q b =
          (TauCeti.Topology.toCechCohomology (ModuleCat.{u} R) q U.opens U.isOpenCover).app Q b :=
        congrArg (fun t ↦ t.app Q b)
          (TauCeti.Topology.toCechCohomology_opens (ModuleCat.{u} R) q U).symm
      rw [hιp, hιq,
        TauCeti.Topology.cechCohomologyCup_toCechCohomology,
        cechCohomologyPullback_toCechCohomology_apply,
        cechCohomologyPullback_toCechCohomology_apply,
        cechCohomologyPullback_toCechCohomology_apply]
      have hR := TauCeti.Topology.cechCohomologyCup_toCechCohomology X μ' hμ' p q n h
        (fun i ↦ (Opens.map f).obj (U.opens i)) (U.isOpenCover.comap f.hom)
        (HomologicalComplex.homologyMap (f.cechComplexPullback U.opens α) p a)
        (HomologicalComplex.homologyMap (f.cechComplexPullback U.opens β) q b)
      exact (congrArg _
        (f.cechComplexPullback_cechComplexCup U.opens μ μ' hμ hμ' α β γ hγ p q n h a b)).trans
        hR.symm
  exact congrArg (fun g ↦ g x y) hΦΨ

/-- **Pullback along a continuous map preserves `cechCohomologyUnitClass`.** -/
theorem cechCohomologyPullback_cechCohomologyUnitClass
    {P : Y.Presheaf (ModuleCat.{u} R)} {P' : X.Presheaf (ModuleCat.{u} R)}
    (α : P ⟶ (TopCat.Presheaf.pushforward (ModuleCat.{u} R) f).obj P')
    (eP : ∀ V : (Opens Y)ᵒᵖ, P.obj V)
    (heP : ∀ {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W), P.map i (eP V) = eP W)
    (eP' : ∀ V : (Opens X)ᵒᵖ, P'.obj V)
    (heP' : ∀ {V W : (Opens X)ᵒᵖ} (i : V ⟶ W), P'.map i (eP' V) = eP' W)
    (hα : ∀ V, α.app V (eP V) = eP' (op ((Opens.map f).obj V.unop))) :
    f.cechCohomologyPullback 0 α (TauCeti.Topology.cechCohomologyUnitClass Y P eP heP) =
      TauCeti.Topology.cechCohomologyUnitClass X P' eP' heP' := by
  let U : PointOpenCover Y := default
  rw [TauCeti.Topology.cechCohomologyUnitClass_eq_toCechCohomology Y P eP heP U.opens U.isOpenCover,
    cechCohomologyPullback_toCechCohomology_apply,
    f.cechComplexPullback_cechUnitClass U.opens α eP heP eP' heP' hα,
    ← TauCeti.Topology.cechCohomologyUnitClass_eq_toCechCohomology X P' eP' heP'
      (fun i ↦ (Opens.map f).obj (U.opens i)) (U.isOpenCover.comap f.hom)]

end Cup

end TopCat.Hom
