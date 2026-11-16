/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Preadditive.Compact

import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import TauCeti.Algebra.Category.ModuleCat.Colimits

/-!
# Sequential homotopy colimits and the Milnor exact sequence

In a pretriangulated category `T` with countable coproducts, a sequential *Milnor homotopy
colimit* of a sequence `X : ℕ ⥤ T` (`X₀ → X₁ → X₂ → ⋯`) is the cone `M` of the
*sequence–difference map* `1 - s : ∐ X.obj ⟶ ∐ X.obj`
(`CategoryTheory.Functor.sequenceDifference`), which is the dual of
`CategoryTheory.Functor.towerDifference` and fits into a distinguished triangle

```
∐ X.obj ──1 - s──▶ ∐ X.obj ──ψ──▶ M ──δ──▶ (∐ X.obj)⟦1⟧.
```

This file establishes the two fundamental mapping properties of a Milnor homotopy colimit
triangle (Neeman, Lemma 1.7.1; Schwede, *Symmetric spectra*, Chapter II, Lemma 5.6):

1. **Mapping out of a compact object:** If `A` is compact for coproducts
   (`TauCeti.IsCompactForCoproducts A`), every morphism `A ⟶ M` factors through some stage
   `X.obj N` (`TauCeti.exists_factor_of_milnorTriangle`), a morphism `A ⟶ X.obj n` vanishes in `M`
   if and only if it is killed by some transition `X.obj n ⟶ X.obj m`
   (`TauCeti.comp_milnorTriangle_eq_zero_iff`), and `Hom(A, M)` is the colimit of the sequence
   `n ↦ Hom(A, X.obj n)` in `AddCommGrpCat` (`TauCeti.isColimitMapCoconeOfMilnorTriangle`).
   Injectivity of the shifted difference map reduces directly to
   `ModuleCat.telescopeDiff_injective`.
2. **The generic Milnor exact sequence:** For any ring `R` and any contravariant homological
   functor `F : Tᵒᵖ ⥤ ModuleCat.{v} R` that takes countable coproducts to products
   (`[PreservesLimitsOfShape (Discrete ℕ) F]`), there is a natural short exact sequence

   ```
   0 ⟶ lim¹ F((Xₙ)⟦1⟧) ⟶ F(M) ⟶ lim F(Xₙ) ⟶ 0
   ```

   expressed directly in terms of `TauCeti.ModuleTower.lim` and `TauCeti.ModuleTower.limOne`
   (`TauCeti.milnorLimOneToObj_injective`, `TauCeti.exact_milnorLimOneToObj_milnorObjToLim`,
   `TauCeti.milnorObjToLim_surjective`, `TauCeti.milnorObjToLim_naturality`,
   `TauCeti.milnorLimOneToObj_naturality`). For an abelian-group-valued contravariant homological
   functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}`, the surjectivity onto compatible families is provided
   directly as `TauCeti.exists_lift_of_milnorTriangle`.

## Main definitions

* `CategoryTheory.Functor.sequenceDifference`: the difference map `1 - s : ∐ X.obj ⟶ ∐ X.obj`
  of a sequence `X : ℕ ⥤ T`.
* `CategoryTheory.Functor.coconeOfSequenceDifference`: a cocone over `X` from a morphism out of
  `∐ X.obj` annihilating `X.sequenceDifference`.
* `TauCeti.cofanOpToPiLinearEquiv`, `TauCeti.cofanOpToPiAddEquiv`: the coordinate equivalences
  for contravariant functors sending a coproduct to a concrete product.
* `TauCeti.coconeOfMilnorTriangle`: the canonical cocone `X ⟶ M` attached to a Milnor triangle.
* `TauCeti.milnorObjToLim`, `TauCeti.milnorLimOneToObj`: the two maps of the Milnor exact
  sequence.

## Main results

* `TauCeti.surjective_comp_of_milnorTriangle`, `TauCeti.exists_factor_of_milnorTriangle`,
  `TauCeti.comp_milnorTriangle_eq_zero_iff`, `TauCeti.isColimitMapCoconeOfMilnorTriangle`:
  mapping out of a compact object into a Milnor homotopy colimit.
* `TauCeti.milnorLimOneToObj_injective`, `TauCeti.exact_milnorLimOneToObj_milnorObjToLim`,
  `TauCeti.milnorObjToLim_surjective`, `TauCeti.milnorObjToLim_bijective_of_subsingleton_limOne`,
  `TauCeti.milnorObjToLim_naturality`, `TauCeti.milnorLimOneToObj_naturality`: the generic Milnor
  exact sequence and its naturality.
* `TauCeti.exists_lift_of_milnorTriangle`: lifting compatible families for `AddCommGrpCat`-valued
  cohomological functors.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. **12** (1962), 337–341.
* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Section 1.6–1.7.
* S. Schwede, *Symmetric spectra*, Chapter II, Definition 5.4 and Lemma 5.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped DirectSum

universe uR w v u

namespace CategoryTheory.Functor

section SequenceDifference

variable {T : Type u} [Category.{v} T] [Preadditive T]
variable (X : ℕ ⥤ T) [HasCoproduct X.obj]

/-- The *sequence–difference map* `1 - s` of a sequence `X₀ → X₁ → ⋯`: the endomorphism
of `∐ X.obj` sending the `n`-th summand `Xₙ` to `ιₙ - φₙ ≫ ιₙ₊₁` (`ι_sequenceDifference`).
Its cone in a pretriangulated category is a Milnor homotopy colimit of `X`. -/
def sequenceDifference : (∐ X.obj) ⟶ (∐ X.obj) :=
  Sigma.desc fun n ↦
    Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1)

@[reassoc (attr := simp)]
lemma ι_sequenceDifference (n : ℕ) :
    Sigma.ι X.obj n ≫ X.sequenceDifference =
      Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) := by
  simp [sequenceDifference]

/-- A morphism `ψ` out of `∐ X.obj` annihilates the sequence–difference map if and only if
its components `Sigma.ι X.obj n ≫ ψ` are compatible with the transition maps `Xₙ ⟶ Xₙ₊₁`. -/
lemma sequenceDifference_comp_eq_zero_iff {Y : T} (ψ : (∐ X.obj) ⟶ Y) :
    X.sequenceDifference ≫ ψ = 0 ↔
      ∀ n, X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) ≫ ψ =
        Sigma.ι X.obj n ≫ ψ := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Sigma.hom_ext _ _ fun n ↦ ?_⟩
  · have h' := Sigma.ι X.obj n ≫= h
    simp only [ι_sequenceDifference_assoc, Preadditive.sub_comp, Category.assoc, comp_zero] at h'
    exact (sub_eq_zero.1 h').symm
  · simp [Preadditive.sub_comp, Category.assoc, h n]

variable {X} in
/-- A morphism out of `∐ X.obj` annihilating the sequence–difference map defines a cocone over
`X`, with components `Sigma.ι X.obj n ≫ ψ`. -/
@[expose, simps pt]
def coconeOfSequenceDifference {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) : Cocone X where
  pt := Y
  ι := NatTrans.ofSequence (fun n ↦ Sigma.ι X.obj n ≫ ψ) fun n ↦ by
    simp [(X.sequenceDifference_comp_eq_zero_iff ψ).1 w n]

@[simp]
lemma coconeOfSequenceDifference_ι_app {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) (n : ℕ) :
    (coconeOfSequenceDifference ψ w).ι.app n = Sigma.ι X.obj n ≫ ψ :=
  (rfl)

/-- If `X.sequenceDifference ≫ ψ = 0`, then the components `Sigma.ι X.obj n ≫ ψ` are
compatible with every composite transition `Xₙ ⟶ Xₘ` (`n ≤ m`). -/
lemma map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero {Y : T} {ψ : (∐ X.obj) ⟶ Y}
    (w : X.sequenceDifference ≫ ψ = 0) {n m : ℕ} (hnm : n ≤ m) :
    X.map (homOfLE hnm) ≫ Sigma.ι X.obj m ≫ ψ = Sigma.ι X.obj n ≫ ψ :=
  (coconeOfSequenceDifference ψ w).w (homOfLE hnm)

/-- The legs of any cocone over `X` annihilate the sequence–difference map. -/
@[reassoc (attr := simp)]
lemma sequenceDifference_desc_ι_app (c : Cocone X) :
    X.sequenceDifference ≫ Sigma.desc (fun n : ℕ ↦ c.ι.app n) = 0 :=
  (X.sequenceDifference_comp_eq_zero_iff _).2 fun n ↦ by simp

/-- The sequence–difference map is natural in morphisms of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma sequenceDifference_naturality {X Y : ℕ ⥤ T} [HasCoproduct X.obj] [HasCoproduct Y.obj]
    (α : X ⟶ Y) :
    X.sequenceDifference ≫ Limits.Sigma.map (fun n ↦ α.app n) =
      Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference :=
  Sigma.hom_ext _ _ fun n ↦ by
    simp only [ι_sequenceDifference_assoc, Sigma.ι_map_assoc, ι_sequenceDifference,
      Preadditive.sub_comp, Preadditive.comp_sub, Sigma.ι_map, Category.assoc,
      α.naturality_assoc]

end SequenceDifference

end CategoryTheory.Functor

namespace TauCeti

section ContravariantProducts

variable {T : Type u} [Category.{v} T]

/-- The equivalence `AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ` equipping each abelian group with its
canonical `ℤ`-module structure. -/
private def addCommGrpToIntMod : AddCommGrpCat.{w} ⥤ ModuleCat.{w} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

private instance : addCommGrpToIntMod.{w}.IsEquivalence := by
  have e : addCommGrpToIntMod.{w} ⋙ forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w} ≅
      𝟭 AddCommGrpCat.{w} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl
  have : (addCommGrpToIntMod.{w} ⋙
      forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso e).2 inferInstance
  exact Functor.isEquivalence_of_comp_right addCommGrpToIntMod.{w}
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w})

/-- A contravariant `ModuleCat R`-valued functor preserving `J`-indexed products identifies its
value on any colimit cofan `c` over `f : J → T` with the concrete product
`∀ j, F.obj (op (f j))`, compatibly with the projections `F.map (c.inj j).op`. -/
def cofanOpToPiLinearEquiv {R : Type uR} [Ring R] {J : Type w} {f : J → T} {c : Cofan f}
    (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] :
    F.obj (op c.pt) ≃ₗ[R] ∀ j, F.obj (op (f j)) :=
  let hFan : IsLimit (Fan.mk (F.obj (op c.pt)) fun j ↦ F.map (c.inj j).op) :=
    (isLimitMapConeFanMkEquiv F (fun j ↦ op (f j)) (fun j ↦ (c.inj j).op)).1
      (isLimitOfPreserves F (Cofan.IsColimit.op hc))
  let e : F.obj (op c.pt) ≅ ModuleCat.of R (∀ j, F.obj (op (f j))) :=
    hFan.conePointUniqueUpToIso (ModuleCat.productConeIsLimit fun j ↦ F.obj (op (f j)))
  LinearEquiv.ofLinearMap e.hom.hom e.inv.hom
    (by rw [← ModuleCat.hom_comp, e.inv_hom_id]; rfl)
    (by rw [← ModuleCat.hom_comp, e.hom_inv_id]; rfl)

@[simp]
theorem cofanOpToPiLinearEquiv_apply {R : Type uR} [Ring R] {J : Type w} {f : J → T} {c : Cofan f}
    (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] (x : F.obj (op c.pt)) (j : J) :
    cofanOpToPiLinearEquiv hc F x j = F.map (c.inj j).op x := by
  let hFan : IsLimit (Fan.mk (F.obj (op c.pt)) fun j ↦ F.map (c.inj j).op) :=
    (isLimitMapConeFanMkEquiv F (fun j ↦ op (f j)) (fun j ↦ (c.inj j).op)).1
      (isLimitOfPreserves F (Cofan.IsColimit.op hc))
  have hproj := hFan.conePointUniqueUpToIso_hom_comp
    (ModuleCat.productConeIsLimit fun j ↦ F.obj (op (f j))) ⟨j⟩
  exact congrArg (fun φ : F.obj (op c.pt) ⟶ F.obj (op (f j)) ↦ φ x) hproj

@[simp]
theorem map_inj_cofanOpToPiLinearEquiv_symm {R : Type uR} [Ring R] {J : Type w} {f : J → T}
    {c : Cofan f} (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] (x : ∀ j, F.obj (op (f j))) (j : J) :
    F.map (c.inj j).op ((cofanOpToPiLinearEquiv hc F).symm x) = x j := by
  rw [← cofanOpToPiLinearEquiv_apply hc F, LinearEquiv.apply_symm_apply]

/-- A contravariant `AddCommGrpCat`-valued functor preserving `J`-indexed products identifies its
value on any colimit cofan `c` over `f : J → T` with the concrete product
`∀ j, E.obj (op (f j))`, compatibly with the projections `E.map (c.inj j).op`. -/
def cofanOpToPiAddEquiv {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E] :
    E.obj (op c.pt) ≃+ ∀ j, E.obj (op (f j)) :=
  have : PreservesLimitsOfShape (Discrete J) (E ⋙ addCommGrpToIntMod) :=
    comp_preservesLimitsOfShape E addCommGrpToIntMod
  (cofanOpToPiLinearEquiv hc (E ⋙ addCommGrpToIntMod)).toAddEquiv

@[simp]
theorem cofanOpToPiAddEquiv_apply {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E]
    (x : E.obj (op c.pt)) (j : J) :
    cofanOpToPiAddEquiv hc E x j = E.map (c.inj j).op x :=
  have : PreservesLimitsOfShape (Discrete J) (E ⋙ addCommGrpToIntMod) :=
    comp_preservesLimitsOfShape E addCommGrpToIntMod
  cofanOpToPiLinearEquiv_apply hc (E ⋙ addCommGrpToIntMod) x j

@[simp]
theorem map_inj_cofanOpToPiAddEquiv_symm {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E]
    (x : ∀ j, E.obj (op (f j))) (j : J) :
    E.map (c.inj j).op ((cofanOpToPiAddEquiv hc E).symm x) = x j := by
  rw [← cofanOpToPiAddEquiv_apply hc E, AddEquiv.apply_symm_apply]

end ContravariantProducts

section CompactMapping

variable {T : Type u} [Category.{v} T] [Preadditive T]

private def coyonedaToHom (A : T) (X : ℕ ⥤ T) (k : ℕ) :
    ↑((X ⋙ preadditiveCoyonedaObj A).obj k) →+ (A ⟶ X.obj k) where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl

private def homToCoyoneda (A : T) (X : ℕ ⥤ T) (k : ℕ) :
    (A ⟶ X.obj k) →+ ↑((X ⋙ preadditiveCoyonedaObj A).obj k) where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Additive equivalence identifying `⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)` with
`⨁ n, (A ⟶ X.obj n)`. -/
private def seqDirectSumEquiv (A : T) (X : ℕ ⥤ T) :
    (⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) ≃+ (⨁ n, (A ⟶ X.obj n)) where
  toFun := DirectSum.map (coyonedaToHom A X)
  invFun := DirectSum.map (homToCoyoneda A X)
  left_inv a := by
    induction a using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n g => rw [DirectSum.map_of, DirectSum.map_of]; rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  right_inv a := by
    induction a using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n g => rw [DirectSum.map_of, DirectSum.map_of]; rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  map_add' := map_add _

private theorem seqDirectSumEquiv_of (A : T) (X : ℕ ⥤ T) (n : ℕ)
    (g : ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    seqDirectSumEquiv A X
        (DirectSum.of (fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)) n g) =
      DirectSum.of (fun k ↦ A ⟶ X.obj k) n (coyonedaToHom A X n g) :=
  DirectSum.map_of (coyonedaToHom A X) n g

/-- Under `coprodComparisonAddHom` and `seqDirectSumEquiv`, postcomposition with
`X.sequenceDifference` agrees with `ModuleCat.telescopeDiff` on `X ⋙ preadditiveCoyonedaObj A`. -/
private theorem coprodComparisonAddHom_telescopeDiff (A : T) (X : ℕ ⥤ T) [HasCoproduct X.obj]
    (a : ⨁ n, ↑((X ⋙ preadditiveCoyonedaObj A).obj n)) :
    coprodComparisonAddHom A X.obj
        (seqDirectSumEquiv A X
          (ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a)) =
      coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X a) ≫ X.sequenceDifference := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n g =>
    rw [← DirectSum.lof_eq_of (End A)ᵐᵒᵖ, ModuleCat.telescopeDiff_lof, map_sub, map_sub,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, seqDirectSumEquiv_of, seqDirectSumEquiv_of,
      coprodComparisonAddHom_of, coprodComparisonAddHom_of, Category.assoc,
      X.ι_sequenceDifference, Preadditive.comp_sub]
    exact congrArg (coyonedaToHom A X n g ≫ Sigma.ι X.obj n - ·)
      (Category.assoc (coyonedaToHom A X n g) (X.map (homOfLE (n.le_add_right 1)))
        (Sigma.ι X.obj (n + 1)))
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, map_add, Preadditive.add_comp, ha, hb]

/-- For a compact object `A`, postcomposition with the sequence–difference map
`X.sequenceDifference : (∐ X.obj) ⟶ (∐ X.obj)` is injective on `A ⟶ ∐ X.obj`. -/
theorem injective_comp_sequenceDifference {A : T} (hA : IsCompactForCoproducts A) (X : ℕ ⥤ T)
    [HasCoproduct X.obj] :
    Function.Injective (fun g : A ⟶ ∐ X.obj ↦ g ≫ X.sequenceDifference) := by
  intro g₁ g₂ hg
  dsimp only at hg
  obtain ⟨a₁', rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 g₁
  obtain ⟨a₂', rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 g₂
  obtain ⟨a₁, rfl⟩ := (seqDirectSumEquiv A X).surjective a₁'
  obtain ⟨a₂, rfl⟩ := (seqDirectSumEquiv A X).surjective a₂'
  rw [← coprodComparisonAddHom_telescopeDiff, ← coprodComparisonAddHom_telescopeDiff] at hg
  have ha := ModuleCat.telescopeDiff_injective (X ⋙ preadditiveCoyonedaObj A)
    ((seqDirectSumEquiv A X).injective ((hA.bijective_coprodComparisonAddHom X.obj).1 hg))
  exact congrArg (fun z ↦ coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X z)) ha

/-- Evaluate a morphism `A ⟶ ∐ X.obj` out of a compact object `A` against the legs of a cocone
over `X ⋙ preadditiveCoyoneda.obj (op A)`. -/
private def evalCoconeOfCompact {X : ℕ ⥤ T} [HasCoproduct X.obj] {A : T}
    (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A))) :
    (A ⟶ ∐ X.obj) →+ s.pt :=
  let leg (k : ℕ) : (A ⟶ X.obj k) →+ s.pt :=
    { toFun := fun f ↦ (s.ι.app k).hom f
      map_zero' := map_zero (s.ι.app k).hom
      map_add' := map_add (s.ι.app k).hom }
  (DirectSum.toAddMonoid leg).comp (hA.homCoprodEquiv X.obj).symm.toAddMonoidHom

private theorem evalCoconeOfCompact_comp_ι {X : ℕ ⥤ T} [HasCoproduct X.obj] {A : T}
    (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A)))
    (n : ℕ) (h : A ⟶ X.obj n) :
    evalCoconeOfCompact hA s (h ≫ Sigma.ι X.obj n) = (s.ι.app n).hom h := by
  dsimp only [evalCoconeOfCompact]
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hA.homCoprodEquiv_symm_comp_ι,
    DirectSum.toAddMonoid_of]
  rfl

private theorem evalCoconeOfCompact_comp_sequenceDifference {X : ℕ ⥤ T} [HasCoproduct X.obj]
    {A : T} (hA : IsCompactForCoproducts A) (s : Cocone (X ⋙ preadditiveCoyoneda.obj (op A)))
    (v : A ⟶ ∐ X.obj) :
    evalCoconeOfCompact hA s (v ≫ X.sequenceDifference) = 0 := by
  obtain ⟨a', rfl⟩ := (hA.bijective_coprodComparisonAddHom X.obj).2 v
  obtain ⟨a, rfl⟩ := (seqDirectSumEquiv A X).surjective a'
  rw [← coprodComparisonAddHom_telescopeDiff, ← hA.homCoprodEquiv_apply X.obj]
  dsimp only [evalCoconeOfCompact]
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n h =>
    rw [← DirectSum.lof_eq_of (End A)ᵐᵒᵖ, ModuleCat.telescopeDiff_lof, map_sub, map_sub,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, seqDirectSumEquiv_of, seqDirectSumEquiv_of,
      DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    have hw := congrArg (fun φ : (preadditiveCoyoneda.obj (op A)).obj (X.obj n) ⟶ s.pt ↦ φ h)
      (s.w (homOfLE (n.le_add_right 1)))
    exact sub_eq_zero.2 hw.symm
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

section Shift

variable [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]

/-- For a compact object `A`, postcomposition with the shifted sequence–difference map
`(X.sequenceDifference)⟦(1 : ℤ)⟧` is injective on `A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧`. -/
theorem injective_comp_shift_sequenceDifference {A : T} (hA : IsCompactForCoproducts A)
    (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    Function.Injective (fun g : A ⟶ (∐ X.obj)⟦(1 : ℤ)⟧ ↦
      g ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧') := by
  intro g₁ g₂ hg
  dsimp only at hg
  let ε := (shiftFunctorCompIsoId T (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom
  let d := X.sequenceDifference
  have hnat :
      (d⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) = ε.app (∐ X.obj) ≫ d :=
    ε.naturality d
  have h1 : (g₁⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ d =
      (g₂⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ d := by
    calc
      (g₁⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ d
          = g₁⟦(-1 : ℤ)⟧' ≫
              (d⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) := by
            rw [Category.assoc, hnat]
      _ = (g₁ ≫ d⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) := by
            rw [← Category.assoc, ← Functor.map_comp]
      _ = (g₂ ≫ d⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) := by rw [hg]
      _ = g₂⟦(-1 : ℤ)⟧' ≫
            (d⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj) := by
            rw [Functor.map_comp, Category.assoc]
      _ = (g₂⟦(-1 : ℤ)⟧' ≫ ε.app (∐ X.obj)) ≫ d := by
            rw [hnat, ← Category.assoc]
  have h2 := injective_comp_sequenceDifference (hA.shift (-1 : ℤ)) X h1
  exact (shiftFunctor T (-1 : ℤ)).map_injective ((cancel_mono (ε.app (∐ X.obj))).1 h2)

end Shift

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

/-- The canonical cocone over `X` with point `M` attached to a Milnor homotopy colimit triangle
`∐ X.obj ⟶ ∐ X.obj ⟶ M ⟶ (∐ X.obj)⟦1⟧`. -/
abbrev coconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
    {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) : Cocone X :=
  X.coconeOfSequenceDifference ψ (comp_distTriang_mor_zero₁₂ _ ht)

/-- Every morphism from a compact object `A` into a Milnor homotopy colimit `M` factors through
the structural map `ψ : ∐ X.obj ⟶ M`. -/
theorem surjective_comp_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) :
    Function.Surjective (fun g : A ⟶ ∐ X.obj ↦ g ≫ ψ) := by
  intro f
  have hrot := rot_of_distTriang _ ht
  have hrot2 := rot_of_distTriang _ hrot
  have hzero : (f ≫ δ) ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 := by
    have hcomp : δ ≫ (-(X.sequenceDifference)⟦(1 : ℤ)⟧') = 0 :=
      comp_distTriang_mor_zero₁₂ _ hrot2
    have hf : f ≫ δ ≫ (-(X.sequenceDifference)⟦(1 : ℤ)⟧') = 0 := by
      rw [hcomp, comp_zero]
    simpa [Preadditive.comp_neg, neg_eq_zero, Category.assoc] using hf
  have hfδ : f ≫ δ = 0 :=
    injective_comp_shift_sequenceDifference hA X (by simpa using hzero)
  have hex := (ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (op A)).map_distinguished_exact _ hrot)
  dsimp only [ShortComplex.map, shortComplexOfDistTriangle, Triangle.rotate] at hex
  exact hex f hfδ

/-- **Factoring out of a compact object into a Milnor homotopy colimit:** every morphism from a
compact object `A` into a Milnor homotopy colimit `M` of `X` factors through some finite stage
`X.obj N`. -/
theorem exists_factor_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) (g : A ⟶ M) :
    ∃ (N : ℕ) (h : A ⟶ X.obj N), g = h ≫ Sigma.ι X.obj N ≫ ψ := by
  obtain ⟨u, rfl⟩ := surjective_comp_of_milnorTriangle ht hA g
  obtain ⟨s, h, rfl⟩ := hA.exists_finset_sum_comp_ι X.obj u
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  let N : ℕ := s.sup id
  refine ⟨N, ∑ n ∈ s.attach,
      h n.1 ≫ X.map (homOfLE (Finset.le_sup (f := id) n.2 : n.1 ≤ N)), ?_⟩
  dsimp only
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  symm
  calc
    ∑ n ∈ s.attach,
        (h n.1 ≫ X.map (homOfLE (Finset.le_sup (f := id) n.2 : n.1 ≤ N))) ≫
          Sigma.ι X.obj N ≫ ψ
        = ∑ n ∈ s.attach, h n.1 ≫ Sigma.ι X.obj n.1 ≫ ψ := by
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          rw [Category.assoc, X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ]
    _ = ∑ n ∈ s, h n ≫ Sigma.ι X.obj n ≫ ψ :=
          Finset.sum_attach s (fun n ↦ h n ≫ Sigma.ι X.obj n ≫ ψ)
    _ = ∑ n ∈ s, (h n ≫ Sigma.ι X.obj n) ≫ ψ := by
          simp only [Category.assoc]

/-- **Kernel criterion for morphisms out of a compact object into a Milnor homotopy colimit:**
a morphism `h : A ⟶ X.obj n` from a compact object `A` vanishes in the Milnor homotopy colimit `M`
if and only if it is annihilated by some transition map `X.obj n ⟶ X.obj m` (`n ≤ m`). -/
theorem comp_milnorTriangle_eq_zero_iff {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) {n : ℕ} (h : A ⟶ X.obj n) :
    h ≫ Sigma.ι X.obj n ≫ ψ = 0 ↔
      ∃ (m : ℕ) (hnm : n ≤ m), h ≫ X.map (homOfLE hnm) = 0 := by
  classical
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  refine ⟨fun hzero ↦ ?_, fun ⟨m, hnm, hm⟩ ↦ by
    rw [← X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ hnm,
      ← Category.assoc, hm, zero_comp]⟩
  have hex := (ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (op A)).map_distinguished_exact _ ht)
  dsimp only [ShortComplex.map, shortComplexOfDistTriangle] at hex
  obtain ⟨v, hv⟩ :=
    hex (h ≫ Sigma.ι X.obj n) ((Category.assoc h (Sigma.ι X.obj n) ψ).trans hzero)
  let v' : A ⟶ ∐ X.obj := v
  let β : ℕ → Type v := fun k ↦ ↑((X ⋙ preadditiveCoyonedaObj A).obj k)
  let a : ⨁ k, β k := (seqDirectSumEquiv A X).symm ((hA.homCoprodEquiv X.obj).symm v')
  let h' : β n := h
  have hdiff : ModuleCat.telescopeDiff (X ⋙ preadditiveCoyonedaObj A) a =
      DirectSum.of β n h' := by
    apply (seqDirectSumEquiv A X).injective
    apply (hA.bijective_coprodComparisonAddHom X.obj).1
    rw [coprodComparisonAddHom_telescopeDiff, seqDirectSumEquiv_of, coprodComparisonAddHom_of]
    have ha : coprodComparisonAddHom A X.obj (seqDirectSumEquiv A X a) = v' := by
      dsimp only [a]
      rw [AddEquiv.apply_symm_apply, ← hA.homCoprodEquiv_apply, AddEquiv.apply_symm_apply]
    exact (congrArg (· ≫ X.sequenceDifference) ha).trans hv
  have hlt (k : ℕ) (hk : k < n) : a k = 0 := by
    induction k with
    | zero => simpa [DirectSum.of_eq_of_ne _ _ _ hk.ne] using congr($hdiff 0)
    | succ k ih =>
      simpa [DirectSum.of_eq_of_ne _ _ _ hk.ne, ih (by omega)] using congr($hdiff (k + 1))
  have han : a n = h' := by
    rcases n with _ | k
    · simpa using congr($hdiff 0)
    · simpa [hlt k (Nat.lt_succ_self k)] using congr($hdiff (k + 1))
  have hge (m : ℕ) (hnm : n ≤ m) :
      a m = (X ⋙ preadditiveCoyonedaObj A).map (homOfLE hnm) h' := by
    induction m, hnm using Nat.le_induction with
    | base =>
      rw [Subsingleton.elim (homOfLE _) (𝟙 n), CategoryTheory.Functor.map_id]
      exact han
    | succ m hnm ih =>
      have h1 := congr($hdiff (m + 1))
      simp only [ModuleCat.telescopeDiff_apply_succ,
        DirectSum.of_eq_of_ne (β := β) n (m + 1) h' (by omega), sub_eq_zero, ih] at h1
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp] at h1
      exact h1
  let m : ℕ := max n (a.support.sup id + 1)
  refine ⟨m, le_max_left _ _, (hge m (le_max_left _ _)).symm.trans <|
    DFinsupp.notMem_support_iff.1 fun hm ↦ ?_⟩
  have hle : m ≤ a.support.sup id := Finset.le_sup (f := id) hm
  omega

/-- For a compact object `A`, `Hom(A, -)` sends any Milnor homotopy colimit triangle to a colimit
cocone in `AddCommGrpCat`. -/
def isColimitMapCoconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} (hA : IsCompactForCoproducts A) :
    IsColimit ((preadditiveCoyoneda.obj (op A)).mapCocone (coconeOfMilnorTriangle ht)) := by
  let F := preadditiveCoyoneda.obj (op A)
  have hsurj := surjective_comp_of_milnorTriangle ht hA
  let lift (g : A ⟶ M) : A ⟶ ∐ X.obj := (hsurj g).choose
  have hlift (g : A ⟶ M) : lift g ≫ ψ = g := (hsurj g).choose_spec
  have hex := (ShortComplex.ab_exact_iff _).1 (F.map_distinguished_exact _ ht)
  dsimp only [ShortComplex.map, shortComplexOfDistTriangle] at hex
  have heval_wd (s : Cocone (X ⋙ F)) {u₁ u₂ : A ⟶ ∐ X.obj}
      (h : u₁ ≫ ψ = u₂ ≫ ψ) :
      evalCoconeOfCompact hA s u₁ = evalCoconeOfCompact hA s u₂ := by
    have hsub : F.map ψ (u₁ - u₂) = 0 :=
      (Preadditive.sub_comp u₁ u₂ ψ).trans (sub_eq_zero.2 h)
    obtain ⟨v, hv⟩ := hex (u₁ - u₂) hsub
    have h0 : evalCoconeOfCompact hA s (u₁ - u₂) = 0 :=
      (congrArg (evalCoconeOfCompact hA s) hv.symm).trans
        (evalCoconeOfCompact_comp_sequenceDifference hA s v)
    exact sub_eq_zero.1 (by simpa [map_sub] using h0)
  refine
    { desc := fun s ↦ AddCommGrpCat.ofHom
        { toFun := fun (g : A ⟶ M) ↦ evalCoconeOfCompact hA s (lift g)
          map_zero' :=
            (heval_wd s (u₂ := 0) ((hlift 0).trans zero_comp.symm)).trans (map_zero _)
          map_add' := fun (g₁ g₂ : A ⟶ M) ↦
            (heval_wd s (u₂ := lift g₁ + lift g₂)
              ((hlift (g₁ + g₂)).trans
                ((Preadditive.add_comp _ _ _ (lift g₁) (lift g₂) ψ).trans
                  (congrArg₂ (· + ·) (hlift g₁) (hlift g₂))).symm)).trans (map_add _ _ _) }
      fac := fun s n ↦ by
        ext (h : A ⟶ X.obj n)
        exact (heval_wd s (u₂ := h ≫ Sigma.ι X.obj n)
          ((hlift _).trans (Category.assoc h (Sigma.ι X.obj n) ψ).symm)).trans
            (evalCoconeOfCompact_comp_ι hA s n h)
      uniq := fun s m hm ↦ by
        ext (g : A ⟶ M)
        obtain ⟨N, h, rfl⟩ := exists_factor_of_milnorTriangle ht hA g
        have hmN := congrArg (fun φ : F.obj (X.obj N) ⟶ s.pt ↦ φ h) (hm N)
        have hfac := (heval_wd s (u₂ := h ≫ Sigma.ι X.obj N)
          ((hlift _).trans (Category.assoc h (Sigma.ι X.obj N) ψ).symm)).trans
            (evalCoconeOfCompact_comp_ι hA s N h)
        exact hmN.trans hfac.symm }

end CompactMapping

section MilnorSequence

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- The shifted coproduct cofan for `X ⋙ shiftFunctor T (1 : ℤ)` with vertex `(∐ X.obj)⟦1⟧` and
inclusions `(Sigma.ι X.obj n)⟦1⟧'`. -/
private abbrev shiftedCoproductCofan (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    Cofan (X ⋙ shiftFunctor T (1 : ℤ)).obj :=
  Cofan.mk ((∐ X.obj)⟦(1 : ℤ)⟧) fun n ↦ (Sigma.ι X.obj n)⟦(1 : ℤ)⟧'

private def isColimit_shiftedCoproductCofan (X : ℕ ⥤ T) [HasCoproduct X.obj] :
    IsColimit (shiftedCoproductCofan X) :=
  (isColimitMapCoconeCofanMkEquiv (shiftFunctor T (1 : ℤ)) X.obj (Sigma.ι X.obj)).1
    (isColimitOfPreserves (shiftFunctor T (1 : ℤ)) (coproductIsCoproduct X.obj))

section ModuleValued

variable {R : Type uR} [Ring R] (F : Tᵒᵖ ⥤ ModuleCat.{v} R)
variable {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
  {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor exact sequence for a contravariant
functor `F : Tᵒᵖ ⥤ ModuleCat R`. -/
def milnorObjToLim (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    F.obj (op M) →ₗ[R] ModuleTower.lim (X.op ⋙ F) :=
  ModuleTower.limLift (X.op ⋙ F) (fun n ↦ (F.map (Sigma.ι X.obj n ≫ ψ).op).hom) fun n ↦ by
    have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
    rw [ModuleTower.transition_def, ← ModuleCat.hom_comp, Functor.comp_map, Functor.op_map,
      Quiver.Hom.unop_op, ← F.map_comp, ← op_comp,
      X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ]

@[simp]
theorem coe_milnorObjToLim_apply (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (u : F.obj (op M)) (n : ℕ) :
    (milnorObjToLim F ht u : ModuleTower.Product (X.op ⋙ F)) n =
      F.map (Sigma.ι X.obj n ≫ ψ).op u :=
  ModuleTower.coe_limLift_apply (X.op ⋙ F) _ _ u n

/-- Naturality of the restriction map `F(M) →ₗ[R] lim F(Xₙ)` with respect to any morphism of
Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorObjToLim_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    milnorObjToLim F htX ∘ₗ (F.map φ.hom₃.op).hom =
      ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α) F) ∘ₗ milnorObjToLim F htY := by
  ext n u
  simp only [LinearMap.comp_apply, ModuleTower.limπ_apply, coe_milnorObjToLim_apply,
    ModuleTower.coe_limMap_apply, ModuleTower.productMap_apply, Functor.whiskerRight_app,
    NatTrans.op_app]
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp, ← F.map_comp,
    ← op_comp, ← op_comp]
  have h23 : ψ ≫ φ.hom₃ = φ.hom₂ ≫ ψ' := φ.comm₂
  have hcomm : Sigma.ι X.obj n ≫ ψ ≫ φ.hom₃ = α.app n ≫ Sigma.ι Y.obj n ≫ ψ' := by
    rw [h23, hφ₂, Sigma.ι_map_assoc]
  rw [Category.assoc, hcomm, ← Category.assoc]

variable [F.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) F]

private theorem cofanOpToPiLinearEquiv_map_sequenceDifference (X : ℕ ⥤ T) [HasCoproduct X.obj]
    (x : F.obj (op (∐ X.obj))) :
    cofanOpToPiLinearEquiv (coproductIsCoproduct X.obj) F (F.map X.sequenceDifference.op x) =
      ModuleTower.shift (X.op ⋙ F)
        (cofanOpToPiLinearEquiv (coproductIsCoproduct X.obj) F x) := by
  funext n
  rw [cofanOpToPiLinearEquiv_apply, ModuleTower.shift_apply, cofanOpToPiLinearEquiv_apply,
    cofanOpToPiLinearEquiv_apply, ModuleTower.transition_def, Functor.comp_map, Functor.op_map,
    Quiver.Hom.unop_op]
  dsimp only [Cofan.inj, Cofan.mk_ι_app]
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp,
    X.ι_sequenceDifference, op_sub, F.map_sub, ← F.map_comp, ← op_comp]
  rfl

private theorem cofanOpToPiLinearEquiv_map_shift_sequenceDifference (X : ℕ ⥤ T)
    [HasCoproduct X.obj] (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F
        (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op y) =
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)
        (cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F y) := by
  funext n
  rw [cofanOpToPiLinearEquiv_apply, ModuleTower.shift_apply, cofanOpToPiLinearEquiv_apply,
    cofanOpToPiLinearEquiv_apply, ModuleTower.transition_def, Functor.comp_map, Functor.op_map,
    Quiver.Hom.unop_op, Functor.comp_map]
  dsimp only [shiftedCoproductCofan, Cofan.inj, Cofan.mk_ι_app]
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp,
    ← (shiftFunctor T (1 : ℤ)).map_comp, X.ι_sequenceDifference,
    (shiftFunctor T (1 : ℤ)).map_sub, (shiftFunctor T (1 : ℤ)).map_comp, op_sub, F.map_sub,
    ← F.map_comp, ← op_comp]
  rfl

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor sequence is surjective. -/
theorem milnorObjToLim_surjective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Surjective (milnorObjToLim F ht) := by
  intro ⟨x, hx⟩
  let e := cofanOpToPiLinearEquiv (coproductIsCoproduct X.obj) F
  have hzero : F.map X.sequenceDifference.op (e.symm x) = 0 := by
    apply e.injective
    rw [cofanOpToPiLinearEquiv_map_sequenceDifference, LinearEquiv.apply_symm_apply, map_zero]
    rw [ModuleTower.lim_eq_ker] at hx
    exact LinearMap.mem_ker.1 hx
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact _ ht)
  dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle] at hex
  obtain ⟨u, hu⟩ := hex (e.symm x) hzero
  have hu' : F.map ψ.op u = e.symm x := hu
  refine ⟨u, Subtype.ext <| funext fun n ↦ ?_⟩
  rw [coe_milnorObjToLim_apply, op_comp, F.map_comp, CategoryTheory.comp_apply, hu']
  exact map_inj_cofanOpToPiLinearEquiv_symm (coproductIsCoproduct X.obj) F x n

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor exact sequence, induced
by `F.map δ.op : F((∐ Xₙ)⟦1⟧) → F(M)`. -/
def milnorLimOneToObj (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) →ₗ[R] F.obj (op M) :=
  let e₁ := cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F
  Submodule.liftQ (LinearMap.range (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)))
    ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) <| by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    have hshift : e₁.symm (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) y) =
        F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op (e₁.symm y) := by
      apply e₁.injective
      rw [LinearEquiv.apply_symm_apply, cofanOpToPiLinearEquiv_map_shift_sequenceDifference,
        LinearEquiv.apply_symm_apply]
    have hδd : δ ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 :=
      comp_distTriang_mor_zero₃₁ _ ht
    rw [hshift, ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, hδd, op_zero,
      F.map_zero]
    rfl

@[simp]
theorem milnorLimOneToObj_mk_map (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    milnorLimOneToObj F ht
        (Submodule.Quotient.mk fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) =
      F.map δ.op y := by
  let e₁ := cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F
  have hy : (fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) = e₁ y :=
    funext fun n ↦ (cofanOpToPiLinearEquiv_apply (isColimit_shiftedCoproductCofan X) F y n).symm
  rw [hy]
  dsimp only [milnorLimOneToObj]
  rw [Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor sequence is
injective. -/
theorem milnorLimOneToObj_injective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Injective (milnorLimOneToObj F ht) := by
  let e₁ := cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hrot2 := rot_of_distTriang _ (rot_of_distTriang _ ht)
  have hex2 := (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact _ hrot2)
  dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle,
    Triangle.rotate] at hex2
  obtain ⟨w, hw⟩ := hex2 (e₁.symm x) hz
  have hw0 : F.map (-(X.sequenceDifference)⟦(1 : ℤ)⟧').op w = e₁.symm x := hw
  refine ⟨-e₁ w, ?_⟩
  rw [map_neg, ← cofanOpToPiLinearEquiv_map_shift_sequenceDifference]
  have hw' : F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op (-w) = e₁.symm x := by
    simpa [op_neg, F.map_neg] using hw0
  rw [← map_neg e₁, ← map_neg (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op).hom, hw',
    LinearEquiv.apply_symm_apply]

/-- Exactness at the middle term of the Milnor sequence
`0 → lim¹ F((Xₙ)⟦1⟧) → F(M) → lim F(Xₙ) → 0`. -/
theorem exact_milnorLimOneToObj_milnorObjToLim
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Exact (milnorLimOneToObj F ht) (milnorObjToLim F ht) := by
  let e := cofanOpToPiLinearEquiv (coproductIsCoproduct X.obj) F
  let e₁ := cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan X) F
  intro u
  constructor
  · intro hu
    have hψ : F.map ψ.op u = 0 := by
      apply e.injective
      rw [map_zero]
      funext n
      have hcoord := congrArg
        (fun v : ModuleTower.lim (X.op ⋙ F) ↦ (v : ModuleTower.Product (X.op ⋙ F)) n) hu
      rw [coe_milnorObjToLim_apply, op_comp, F.map_comp, CategoryTheory.comp_apply] at hcoord
      dsimp only [e]
      rw [cofanOpToPiLinearEquiv_apply]
      exact hcoord
    have hrot := rot_of_distTriang _ ht
    have hex := (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact _ hrot)
    dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle,
      Triangle.rotate] at hex
    obtain ⟨y, hy⟩ := hex u hψ
    refine ⟨Submodule.Quotient.mk (e₁ y), ?_⟩
    dsimp only [milnorLimOneToObj]
    rw [Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    ext n
    rw [ModuleTower.limπ_apply, ModuleTower.limπ_apply, coe_milnorObjToLim_apply]
    dsimp only [milnorLimOneToObj]
    have hψδ : ψ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ ht
    rw [Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ← CategoryTheory.comp_apply, ← F.map_comp, ← op_comp, Category.assoc, hψδ, comp_zero,
      op_zero, F.map_zero]
    rfl

/-- When `lim¹ F((Xₙ)⟦1⟧)` vanishes, the Milnor restriction map `F(M) →ₗ[R] lim F(Xₙ)`
is bijective. -/
theorem milnorObjToLim_bijective_of_subsingleton_limOne
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [Subsingleton (ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))] :
    Function.Bijective (milnorObjToLim F ht) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, milnorObjToLim_surjective F ht⟩
  obtain ⟨z, rfl⟩ := (exact_milnorLimOneToObj_milnorObjToLim F ht u).1 hu
  rw [Subsingleton.elim z 0, map_zero]

/-- Naturality of the connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` with respect to any morphism
of Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorLimOneToObj_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.map φ.hom₃.op).hom ∘ₗ milnorLimOneToObj F htY =
      milnorLimOneToObj F htX ∘ₗ
        ModuleTower.limOneMap
          (Functor.whiskerRight
            (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) := by
  let eY := cofanOpToPiLinearEquiv (isColimit_shiftedCoproductCofan Y) F
  ext x
  obtain ⟨y, rfl⟩ := eY.surjective x
  have hprod :
      ModuleTower.productMap
          (Functor.whiskerRight
            (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) (eY y) =
        fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op
          (F.map (φ.hom₁⟦(1 : ℤ)⟧').op y) := by
    funext n
    rw [ModuleTower.productMap_apply, Functor.whiskerRight_app, NatTrans.op_app,
      Functor.whiskerRight_app]
    dsimp only [eY]
    rw [cofanOpToPiLinearEquiv_apply]
    dsimp only [shiftedCoproductCofan, Cofan.inj, Cofan.mk_ι_app]
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp,
      ← F.map_comp, ← op_comp, ← op_comp, ← (shiftFunctor T (1 : ℤ)).map_comp,
      ← (shiftFunctor T (1 : ℤ)).map_comp, hφ₁, Sigma.ι_map]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, ModuleTower.limOneMap_mk, hprod,
    milnorLimOneToObj_mk_map]
  have hL : milnorLimOneToObj F htY (Submodule.Quotient.mk (eY y)) = F.map δ'.op y := by
    have heY : eY y = fun n ↦ F.map ((Sigma.ι Y.obj n)⟦(1 : ℤ)⟧').op y :=
      funext fun n ↦ cofanOpToPiLinearEquiv_apply (isColimit_shiftedCoproductCofan Y) F y n
    rw [heY, milnorLimOneToObj_mk_map]
  have hcomm : δ ≫ φ.hom₁⟦(1 : ℤ)⟧' = φ.hom₃ ≫ δ' := φ.comm₃
  rw [hL, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← F.map_comp,
    ← F.map_comp, ← op_comp, ← op_comp, hcomm]

end ModuleValued

section AddCommGrpValued

/-- **Milnor lifting for `AddCommGrpCat`-valued cohomological functors:** for a contravariant
homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` preserving countable products and any Milnor
homotopy colimit triangle of `X : ℕ ⥤ T`, every compatible family
`x : ∀ n, E.obj (op (X.obj n))` lifts to an element `u : E.obj (op M)` restricting to `x n`
along each `Sigma.ι X.obj n ≫ ψ`. -/
theorem exists_lift_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) E]
    (x : ∀ n, E.obj (op (X.obj n)))
    (hx : ∀ n, E.map (X.map (homOfLE (Nat.le_add_right n 1))).op (x (n + 1)) = x n) :
    ∃ u : E.obj (op M), ∀ n, E.map (Sigma.ι X.obj n ≫ ψ).op u = x n := by
  have : PreservesLimitsOfShape (Discrete ℕ) (E ⋙ addCommGrpToIntMod) :=
    comp_preservesLimitsOfShape E addCommGrpToIntMod
  have : (E ⋙ addCommGrpToIntMod).IsHomological :=
    { map_zero := fun _ _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ by
        simp [addCommGrpToIntMod]; rfl
      exact := fun s hs ↦ (ShortComplex.moduleCat_exact_iff _).2 <|
        (ShortComplex.ab_exact_iff _).1 (E.map_distinguished_exact s hs) }
  obtain ⟨u, hu⟩ := milnorObjToLim_surjective (E ⋙ addCommGrpToIntMod) ht
    ⟨x, (ModuleTower.mem_lim (X.op ⋙ E ⋙ addCommGrpToIntMod)).2 fun n ↦ by
      rw [ModuleTower.transition_def]
      exact hx n⟩
  refine ⟨u, fun n ↦ ?_⟩
  have hn :=
    congrArg (fun v : ModuleTower.lim (X.op ⋙ (E ⋙ addCommGrpToIntMod)) ↦ v.1 n) hu
  rw [coe_milnorObjToLim_apply] at hn
  exact hn

end AddCommGrpValued

end MilnorSequence

end TauCeti
