/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Category.Grp.ZModuleEquivalence
public import TauCeti.Algebra.Category.ModuleCat.Tower.AddCommGroup
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Compact
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.ModuleCat
public import TauCeti.CategoryTheory.Shift.Limits

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import TauCeti.CategoryTheory.ConcreteCategory.Basic
import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic
import TauCeti.CategoryTheory.Preadditive.Yoneda
import TauCeti.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Sequential homotopy colimits and the Milnor exact sequence

In a pretriangulated category `T` with countable coproducts, a sequential *Milnor homotopy
colimit* of `X : ℕ ⥤ T` (`X₀ → X₁ → ⋯`) is the cone `M` of `X.sequenceDifference`
(`CategoryTheory.Functor.sequenceDifference`), fitting into a distinguished triangle
`∐ X.obj ──1 - s──▶ ∐ X.obj ──ψ──▶ M ──δ──▶ (∐ X.obj)⟦1⟧`.

We establish:
1. **Mapping out of a compact object:** for `A` whose corepresented functor `Hom(A, -)` preserves
   countable coproducts (`PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))`),
   morphisms `A ⟶ M` factor through some `X.obj N` (`exists_factor_of_milnorTriangle`),
   `Hom(A, M)` is the colimit of `Hom(A, X.obj n)` (`isColimitMapCoconeOfMilnorTriangle`), and
   morphisms `A ⟶ X.obj n` vanish in `M` iff killed by some transition
   (`comp_ι_comp_eq_zero_iff_of_milnorTriangle`).
2. **The generic Milnor exact sequence:** for `F : Tᵒᵖ ⥤ ModuleCat.{s} R` homological taking
   countable coproducts to products, `0 ⟶ lim¹ F((Xₙ)⟦1⟧) ⟶ F(M) ⟶ lim F(Xₙ) ⟶ 0` is a
   natural short exact sequence (`CategoryTheory.Functor.milnorShortComplex`,
   `CategoryTheory.Functor.milnorShortComplexMap`,
   `CategoryTheory.Functor.shortExact_milnorShortComplex`), together with the corresponding
   `AddCommGrpCat`-valued Milnor sequence (`CategoryTheory.Functor.milnorShortComplexAdd`,
   `CategoryTheory.Functor.milnorShortComplexAddMap`,
   `CategoryTheory.Functor.milnorShortComplexAddIso`,
   `CategoryTheory.Functor.shortExact_milnorShortComplexAdd`) and
   `TauCeti.exists_lift_of_milnorTriangle`.

## Main definitions

* `TauCeti.coconeOfMilnorTriangle`
* `CategoryTheory.Functor.milnorObjToLim`, `CategoryTheory.Functor.milnorLimOneToObj`,
  `CategoryTheory.Functor.milnorShortComplex`, `CategoryTheory.Functor.milnorShortComplexMap`
* `CategoryTheory.Functor.milnorObjToLimAdd`, `CategoryTheory.Functor.milnorLimOneToObjAdd`,
  `CategoryTheory.Functor.milnorShortComplexAdd`, `CategoryTheory.Functor.milnorShortComplexAddMap`,
  `CategoryTheory.Functor.milnorShortComplexAddIso`

## Main results

* `TauCeti.surjective_comp_of_milnorTriangle`, `TauCeti.isColimitMapCoconeOfMilnorTriangle`,
  `TauCeti.exists_factor_of_milnorTriangle`, `TauCeti.comp_ι_comp_eq_zero_iff_of_milnorTriangle`,
  `TauCeti.exists_lift_of_milnorTriangle`
* `CategoryTheory.Functor.milnorLimOneToObj_injective`,
  `CategoryTheory.Functor.exact_milnorLimOneToObj_milnorObjToLim`,
  `CategoryTheory.Functor.milnorObjToLim_surjective`,
  `CategoryTheory.Functor.shortExact_milnorShortComplex`,
  `CategoryTheory.Functor.milnorObjToLim_bijective_of_subsingleton_limOne`,
  `CategoryTheory.Functor.milnorObjToLim_naturality`,
  `CategoryTheory.Functor.milnorLimOneToObj_naturality`
* `CategoryTheory.Functor.milnorLimOneToObjAdd_injective`,
  `CategoryTheory.Functor.exact_milnorLimOneToObjAdd_milnorObjToLimAdd`,
  `CategoryTheory.Functor.milnorObjToLimAdd_surjective`,
  `CategoryTheory.Functor.shortExact_milnorShortComplexAdd`,
  `CategoryTheory.Functor.milnorObjToLimAdd_bijective_of_subsingleton_limOne`,
  `CategoryTheory.Functor.milnorObjToLimAdd_naturality`,
  `CategoryTheory.Functor.milnorLimOneToObjAdd_naturality`,
  `CategoryTheory.Functor.milnorShortComplexAddIso_naturality`

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. **12** (1962), 337–341.
* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Section 1.6–1.7.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4 and Lemma 5.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

universe uR s v u

namespace TauCeti

section CompactMapping

variable {T : Type u} [Category.{v} T] [Preadditive T]
  [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- The canonical cocone over `X` with point `M` attached to a Milnor homotopy colimit triangle
`∐ X.obj ⟶ ∐ X.obj ⟶ M ⟶ (∐ X.obj)⟦1⟧`. -/
@[expose]
def coconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
    {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) : Cocone X :=
  X.coconeOfSequenceDifference ψ (comp_distTriang_mor_zero₁₂ _ ht)

@[simp]
theorem coconeOfMilnorTriangle_pt {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
    {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    (coconeOfMilnorTriangle ht).pt = M :=
  rfl

@[simp]
theorem coconeOfMilnorTriangle_ι_app {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) (n : ℕ) :
    (coconeOfMilnorTriangle ht).ι.app n = Sigma.ι X.obj n ≫ ψ :=
  rfl

/-- If `Hom(A, -)` preserves countable coproducts, then postcomposition with the structural map
`ψ : ∐ X.obj ⟶ M` of a Milnor homotopy colimit triangle is surjective on `A ⟶ M`. -/
theorem surjective_comp_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))] :
    Function.Surjective (fun g : A ⟶ ∐ X.obj ↦ g ≫ ψ) := fun f ↦ by
  have hfδ : f ≫ δ = 0 := X.injective_comp_shift_sequenceDifference <| by
    have hδ : δ ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ ht
    dsimp only; rw [Category.assoc, hδ, comp_zero, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ ht f hfδ
  exact ⟨g, hg.symm⟩

/-- If `Hom(A, -)` preserves countable coproducts, then `Hom(A, -)` sends any Milnor homotopy
colimit triangle to a colimit cocone in `AddCommGrpCat`. -/
def isColimitMapCoconeOfMilnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))] :
    IsColimit ((preadditiveCoyoneda.obj (op A)).mapCocone (coconeOfMilnorTriangle ht)) := by
  let F := preadditiveCoyoneda.obj (op A)
  have hepi : Epi (F.map ψ) :=
    ConcreteCategory.epi_of_surjective (F.map ψ) (surjective_comp_of_milnorTriangle ht)
  let S := (shortComplexOfDistTriangle (Triangle.mk X.sequenceDifference ψ δ) ht).map F
  have hex := F.map_distinguished_exact _ ht
  have : Epi S.g := hepi
  have hcomp := X.sigmaComparison_comp_map_sequenceDifference F
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  have hz : (X ⋙ F).sequenceDifference ≫ sigmaComparison F X.obj ≫ F.map ψ = 0 := by
    simp only [← X.sigmaComparison_comp_map_sequenceDifference_assoc, ← F.map_comp, hψ, F.map_zero,
      comp_zero]
  let iso : ∐ (X ⋙ F).obj ≅ F.obj (∐ X.obj) := asIso (sigmaComparison F X.obj)
  have hcok : IsColimit (CokernelCofork.ofπ (sigmaComparison F X.obj ≫ F.map ψ) hz) :=
    IsCokernel.ofIso _ hex.gIsCokernel _ iso.symm iso.symm (Iso.refl _)
      (by simp [iso, hcomp]) (by simp [iso])
  exact IsColimit.ofIsoColimit ((X ⋙ F).isColimitCoconeOfSequenceDifference hcok)
    (Cocone.ext (Iso.refl _) fun n ↦
      (Category.comp_id _).trans <|
        (Functor.coconeOfSequenceDifference_ι_app (X ⋙ F) _ _ n).trans <|
          (congrArg (Sigma.ι (X ⋙ F).obj n ≫ ·) (Cofork.π_ofπ _ _)).trans <|
            (ι_comp_sigmaComparison_assoc F X.obj n (F.map ψ)).trans <|
              (F.map_comp (Sigma.ι X.obj n) ψ).symm.trans <|
                (congrArg F.map (coconeOfMilnorTriangle_ι_app ht n).symm).trans
                  (Functor.mapCocone_ι_app F (coconeOfMilnorTriangle ht) n).symm)

/-- **Factoring out of a compact object into a Milnor homotopy colimit:** if `Hom(A, -)` preserves
countable coproducts, then every morphism from `A` into a Milnor homotopy colimit `M` of `X`
factors through some finite stage `X.obj N`. -/
theorem exists_factor_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))]
    (g : A ⟶ M) :
    ∃ (N : ℕ) (h : A ⟶ X.obj N), g = h ≫ Sigma.ι X.obj N ≫ ψ := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget AddCommGrpCat.{v})
  obtain ⟨N, (h : A ⟶ X.obj N), hh⟩ := Concrete.isColimit_exists_rep
    (X ⋙ preadditiveCoyoneda.obj (op A)) (isColimitMapCoconeOfMilnorTriangle ht (A := A)) g
  rw [Functor.mapCocone_ι_app, preadditiveCoyoneda_obj_map_apply,
    coconeOfMilnorTriangle_ι_app] at hh
  exact ⟨N, h, hh.symm⟩

/-- **Kernel criterion for morphisms out of a compact object into a Milnor homotopy colimit:**
if `Hom(A, -)` preserves countable coproducts, a morphism `h : A ⟶ X.obj n` vanishes in the Milnor
homotopy colimit `M` if and only if it is annihilated by some transition map `X.obj n ⟶ X.obj m`
(`n ≤ m`). -/
theorem comp_ι_comp_eq_zero_iff_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {A : T} [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op A))]
    {n : ℕ} (h : A ⟶ X.obj n) :
    h ≫ Sigma.ι X.obj n ≫ ψ = 0 ↔ ∃ (m : ℕ) (hnm : n ≤ m), h ≫ X.map (homOfLE hnm) = 0 := by
  have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
  refine ⟨fun hzero ↦ ?_, fun ⟨m, hnm, hm⟩ ↦ by
    rw [← X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ hnm,
      ← Category.assoc, hm, zero_comp]⟩
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget AddCommGrpCat.{v})
  obtain ⟨m, f, hm⟩ := Concrete.exists_map_eq_zero_of_ι_eq_zero
    (X ⋙ preadditiveCoyoneda.obj (op A)) (isColimitMapCoconeOfMilnorTriangle ht (A := A))
    (n := n) (x := h) (by
      rw [Functor.mapCocone_ι_app, preadditiveCoyoneda_obj_map_apply, coconeOfMilnorTriangle_ι_app]
      exact hzero)
  rw [Functor.comp_map, preadditiveCoyoneda_obj_map_apply] at hm
  exact ⟨m, leOfHom f, by rwa [Subsingleton.elim (homOfLE (leOfHom f)) f]⟩

end CompactMapping

end TauCeti

section MilnorSequence

namespace CategoryTheory.Functor

open TauCeti

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

section ModuleValued

variable {R : Type uR} [Ring R] (F : Tᵒᵖ ⥤ ModuleCat.{s} R)
variable {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
  {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor exact sequence for a contravariant
functor `F : Tᵒᵖ ⥤ ModuleCat R`. -/
def milnorObjToLim (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    F.obj (op M) →ₗ[R] ModuleTower.lim (X.op ⋙ F) :=
  ModuleTower.limLift (X.op ⋙ F) (fun n ↦ (F.map (Sigma.ι X.obj n ≫ ψ).op).hom) fun n ↦ by
    have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
    ext x
    simpa [ModuleTower.transition_def, map_op_comp_apply] using
      congrArg (fun ξ ↦ F.map ξ.op x)
        (X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ (n.le_add_right 1))

@[simp]
theorem coe_milnorObjToLim_apply (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (u : F.obj (op M)) (n : ℕ) :
    (F.milnorObjToLim ht u : ModuleTower.Product (X.op ⋙ F)) n =
      F.map (Sigma.ι X.obj n ≫ ψ).op u :=
  ModuleTower.coe_limLift_apply (X.op ⋙ F) _ _ u n

/-- Naturality of the restriction map `F(M) →ₗ[R] lim F(Xₙ)` with respect to any morphism of
Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorObjToLim_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T) (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    F.milnorObjToLim htX ∘ₗ (F.map φ.hom₃.op).hom =
      ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α) F) ∘ₗ F.milnorObjToLim htY := by
  ext n u
  have hcomm2 : ψ ≫ φ.hom₃ = φ.hom₂ ≫ ψ' := φ.comm₂
  have hcomm : (Sigma.ι X.obj n ≫ ψ) ≫ φ.hom₃ = α.app n ≫ Sigma.ι Y.obj n ≫ ψ' := by
    rw [Category.assoc, hcomm2, hφ₂, Sigma.ι_map_assoc]
  simp only [LinearMap.comp_apply, ModuleTower.limπ_apply, coe_milnorObjToLim_apply,
    ModuleTower.coe_limMap_apply, ModuleTower.productMap_apply, Functor.whiskerRight_app,
    NatTrans.op_app]
  exact F.map_op_apply_eq_of_comp_eq hcomm u

section Additive

variable [F.Additive]

private theorem map_δ_comp_cofanOpToPiLinearEquiv_symm_shift
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    ((F.map δ.op).hom ∘ₗ
        ((isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv
          F).symm.toLinearMap) ∘ₗ
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) = 0 := by
  let e₁ := (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  ext1 y
  have hshift : e₁.symm (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) y) =
      F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op (e₁.symm y) := e₁.injective <| by
    rw [LinearEquiv.apply_symm_apply, cofanOpToPiLinearEquiv_map_shift_sequenceDifference,
      LinearEquiv.apply_symm_apply]
  have hδ : δ ≫ (X.sequenceDifference)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ ht
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hshift,
    ← map_op_comp_apply, hδ, op_zero, F.map_zero]
  simp

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor exact sequence, induced
by `F.map δ.op : F((∐ Xₙ)⟦1⟧) → F(M)`. -/
def milnorLimOneToObj (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) →ₗ[R] F.obj (op M) :=
  let e₁ := (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  Submodule.liftQ (LinearMap.range (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)))
    ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) <| by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (F.map_δ_comp_cofanOpToPiLinearEquiv_symm_shift ht) y

/-- Evaluation of `milnorLimOneToObj` on a quotient representative `Submodule.Quotient.mk x`. -/
@[simp]
theorem milnorLimOneToObj_mk (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    (x : ModuleTower.Product ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)) :
    F.milnorLimOneToObj ht (Submodule.Quotient.mk x) =
      F.map δ.op
        (((isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F).symm x) := by
  rw [milnorLimOneToObj, Submodule.liftQ_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]

@[simp high]
theorem milnorLimOneToObj_mk_map (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    F.milnorLimOneToObj ht
        (Submodule.Quotient.mk fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) =
      F.map δ.op y := by
  let e₁ := (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  have he₁ : (fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) = e₁ y :=
    funext fun n ↦
      ((isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv_apply F y n).symm
  rw [he₁, F.milnorLimOneToObj_mk ht, e₁.symm_apply_apply]

/-- Naturality of the connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` with respect to any morphism
of Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorLimOneToObj_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.map φ.hom₃.op).hom ∘ₗ F.milnorLimOneToObj htY = F.milnorLimOneToObj htX ∘ₗ
      ModuleTower.limOneMap (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) := by
  let eY := (isColimitShiftedCoproductCofan Y.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  ext x
  obtain ⟨y, rfl⟩ := eY.surjective x
  have hprod :
      ModuleTower.productMap (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) (eY y) =
        fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op (F.map (φ.hom₁⟦(1 : ℤ)⟧').op y) := by
    funext n
    have hsq : (Sigma.ι X.obj n)⟦(1 : ℤ)⟧' ≫ φ.hom₁⟦(1 : ℤ)⟧' =
        (α.app n)⟦(1 : ℤ)⟧' ≫ (Sigma.ι Y.obj n)⟦(1 : ℤ)⟧' := by
      rw [← (shiftFunctor T (1 : ℤ)).map_comp, hφ₁, Sigma.ι_map,
        (shiftFunctor T (1 : ℤ)).map_comp]
    simp only [ModuleTower.productMap_apply, Functor.whiskerRight_app, NatTrans.op_app,
      eY, IsColimit.cofanOpToPiLinearEquiv_apply, Cofan.inj]
    exact (F.map_op_apply_eq_of_comp_eq hsq y).symm
  have hL : F.milnorLimOneToObj htY (Submodule.Quotient.mk (eY y)) = F.map δ'.op y := by
    rw [F.milnorLimOneToObj_mk htY, eY.symm_apply_apply]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, hL, ModuleTower.limOneMap_mk, hprod,
    milnorLimOneToObj_mk_map]
  exact (F.map_op_apply_eq_of_comp_eq φ.comm₃ y).symm

/-- The composite `lim¹ F((Xₙ)⟦1⟧) → F(M) → lim F(Xₙ)` of the Milnor sequence is zero. -/
@[simp]
theorem milnorObjToLim_comp_milnorLimOneToObj
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    F.milnorObjToLim ht ∘ₗ F.milnorLimOneToObj ht = 0 := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine Subtype.ext <| funext fun n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
    coe_milnorObjToLim_apply, F.milnorLimOneToObj_mk ht]
  have hcomp : ψ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ ht
  rw [← map_op_comp_apply, Category.assoc, hcomp, comp_zero, op_zero, F.map_zero]
  simp

/-- The Milnor short complex `lim¹ F((Xₙ)⟦1⟧) ⟶ F(M) ⟶ lim F(Xₙ)` in `ModuleCat R`
attached to a Milnor homotopy colimit triangle. -/
@[expose]
def milnorShortComplex (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    ShortComplex (ModuleCat.{s} R) :=
  ShortComplex.mk (ModuleCat.ofHom (F.milnorLimOneToObj ht))
    (ModuleCat.ofHom (F.milnorObjToLim ht))
    (ModuleCat.hom_ext (F.milnorObjToLim_comp_milnorLimOneToObj ht))

@[simp]
theorem milnorShortComplex_X₁ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).X₁ =
      ModuleCat.of R (ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)) :=
  rfl

@[simp]
theorem milnorShortComplex_X₂ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).X₂ = F.obj (op M) :=
  rfl

@[simp]
theorem milnorShortComplex_X₃ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).X₃ = ModuleCat.of R (ModuleTower.lim (X.op ⋙ F)) :=
  rfl

@[simp]
theorem milnorShortComplex_f (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).f = ModuleCat.ofHom (F.milnorLimOneToObj ht) :=
  rfl

@[simp]
theorem milnorShortComplex_g (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).g = ModuleCat.ofHom (F.milnorObjToLim ht) :=
  rfl

/-- The contravariant morphism of Milnor short complexes
`F.milnorShortComplex htY ⟶ F.milnorShortComplex htX` induced by a morphism of Milnor triangles
`φ` extending a natural transformation `α : X ⟶ Y`. -/
@[expose]
def milnorShortComplexMap {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    F.milnorShortComplex htY ⟶ F.milnorShortComplex htX where
  τ₁ := ModuleCat.ofHom (ModuleTower.limOneMap (Functor.whiskerRight
    (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F))
  τ₂ := F.map φ.hom₃.op
  τ₃ := ModuleCat.ofHom (ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α) F))
  comm₁₂ := ModuleCat.hom_ext (F.milnorLimOneToObj_naturality htX htY α φ hφ₁).symm
  comm₂₃ := ModuleCat.hom_ext (F.milnorObjToLim_naturality htX htY α φ hφ₂)

@[simp]
theorem milnorShortComplexMap_τ₁ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.milnorShortComplexMap htX htY α φ hφ₁ hφ₂).τ₁ =
      ModuleCat.ofHom (ModuleTower.limOneMap (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F)) :=
  rfl

@[simp]
theorem milnorShortComplexMap_τ₂ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.milnorShortComplexMap htX htY α φ hφ₁ hφ₂).τ₂ = F.map φ.hom₃.op :=
  rfl

@[simp]
theorem milnorShortComplexMap_τ₃ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.milnorShortComplexMap htX htY α φ hφ₁ hφ₂).τ₃ =
      ModuleCat.ofHom (ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α) F)) :=
  rfl

end Additive

section Homological

variable [F.IsHomological]

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor sequence is surjective. -/
theorem milnorObjToLim_surjective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F] :
    Function.Surjective (F.milnorObjToLim ht) := fun ⟨x, hx⟩ ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  have hzero : F.map X.sequenceDifference.op (e.symm x) = 0 := e.injective <| by
    rw [cofanOpToPiLinearEquiv_map_sequenceDifference, LinearEquiv.apply_symm_apply, map_zero]
    exact LinearMap.mem_ker.1 (ModuleTower.lim_eq_ker (X.op ⋙ F) ▸ hx)
  obtain ⟨u, hu⟩ := F.exists_map_op_mor₂_eq_of_moduleCat ht hzero
  simp only [Triangle.mk_mor₂] at hu
  refine ⟨u, Subtype.ext <| funext fun n ↦ ?_⟩
  rw [coe_milnorObjToLim_apply, map_op_comp_apply, hu]
  exact (coproductIsCoproduct X.obj).map_inj_cofanOpToPiLinearEquiv_symm F x n

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor sequence is
injective. -/
theorem milnorLimOneToObj_injective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    Function.Injective (F.milnorLimOneToObj ht) := by
  let e₁ := (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  have hex : Function.Exact (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))
      ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) :=
    Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e₁) (e₂ := e₁)
      (e₃ := LinearEquiv.refl R _)
      (LinearMap.ext fun x ↦ (cofanOpToPiLinearEquiv_map_shift_sequenceDifference F X x).symm)
      (LinearMap.ext fun _ ↦ by simp)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (F.map_distinguished_op_exact₃₁ _ ht))
  exact LinearMap.injective_range_liftQ_of_exact hex

/-- Exactness at the middle term of the Milnor sequence
`0 → lim¹ F((Xₙ)⟦1⟧) → F(M) → lim F(Xₙ) → 0`. -/
theorem exact_milnorLimOneToObj_milnorObjToLim
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    Function.Exact (F.milnorLimOneToObj ht) (F.milnorObjToLim ht) := fun u ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  let e₁ := (isColimitShiftedCoproductCofan X.obj (1 : ℤ)).cofanOpToPiLinearEquiv F
  refine ⟨fun hu ↦ ?_, ?_⟩
  · have hψ : F.map ψ.op u = 0 := e.injective <| by
      rw [map_zero]; funext n
      have hcoord := congrArg
        (fun v : ModuleTower.lim (X.op ⋙ F) ↦ (v : ModuleTower.Product (X.op ⋙ F)) n) hu
      rw [coe_milnorObjToLim_apply, map_op_comp_apply] at hcoord
      dsimp only [e]; rw [IsColimit.cofanOpToPiLinearEquiv_apply]; exact hcoord
    obtain ⟨y, hy⟩ := F.exists_map_op_mor₂_eq_of_moduleCat (rot_of_distTriang _ ht) hψ
    simp only [Triangle.rotate_mor₂, Triangle.mk_mor₃] at hy
    refine ⟨Submodule.Quotient.mk (e₁ y), ?_⟩
    rw [F.milnorLimOneToObj_mk ht, e₁.symm_apply_apply, hy]
  · rintro ⟨z, rfl⟩
    exact LinearMap.congr_fun (F.milnorObjToLim_comp_milnorLimOneToObj ht) z

/-- The Milnor sequence `0 ⟶ lim¹ F((Xₙ)⟦1⟧) ⟶ F(M) ⟶ lim F(Xₙ) ⟶ 0` is short exact
for any contravariant homological functor `F : Tᵒᵖ ⥤ ModuleCat R` preserving the countable
products of `X` and `X⟦1⟧`. -/
theorem shortExact_milnorShortComplex
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F] :
    (F.milnorShortComplex ht).ShortExact :=
  ModuleCat.shortComplex_shortExact (F.milnorShortComplex ht)
    (F.exact_milnorLimOneToObj_milnorObjToLim ht)
    (F.milnorLimOneToObj_injective ht)
    (F.milnorObjToLim_surjective ht)

/-- When `lim¹ F((Xₙ)⟦1⟧)` vanishes, the Milnor restriction map `F(M) →ₗ[R] lim F(Xₙ)`
is bijective. -/
theorem milnorObjToLim_bijective_of_subsingleton_limOne
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) F]
    [Subsingleton (ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))] :
    Function.Bijective (F.milnorObjToLim ht) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, F.milnorObjToLim_surjective ht⟩
  obtain ⟨z, rfl⟩ := (F.exact_milnorLimOneToObj_milnorObjToLim ht u).1 hu
  rw [Subsingleton.elim z 0, map_zero]

end Homological

end ModuleValued

section AddCommGrpValued

open TauCeti.CompactCoefficients

variable (E : Tᵒᵖ ⥤ AddCommGrpCat.{s})
variable {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T} {ψ : (∐ X.obj) ⟶ M}
  {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}

/-- The restriction map `E(M) →+ lim E(Xₙ)` of the Milnor exact sequence for a contravariant
functor `E : Tᵒᵖ ⥤ AddCommGrpCat`, valued in `CompactCoefficients.Tower.lim`. -/
def milnorObjToLimAdd (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    E.obj (op M) →+ (Tower.ofFunctor (X.op ⋙ E)).lim :=
  (Tower.ofFunctorLimEquiv (X.op ⋙ E)).symm.toAddMonoidHom.comp
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht).toAddMonoidHom

@[simp]
theorem coe_milnorObjToLimAdd_apply (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (u : E.obj (op M)) (n : ℕ) :
    (E.milnorObjToLimAdd ht u : ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n =
      E.map (Sigma.ι X.obj n ≫ ψ).op u := by
  have h1 : (E.milnorObjToLimAdd ht u : ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n =
      ((Tower.ofFunctorLimEquiv (X.op ⋙ E)).symm
        (((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht) u) :
        ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n :=
    rfl
  exact h1.trans <| (Tower.coe_ofFunctorLimEquiv_symm_apply (X.op ⋙ E) _ n).trans
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).coe_milnorObjToLim_apply ht u n)

/-- Naturality of the restriction map `E(M) →+ lim E(Xₙ)` with respect to any morphism of
Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorObjToLimAdd_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T) (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (E.milnorObjToLimAdd htX).comp (E.map φ.hom₃.op).hom =
      (Tower.Hom.ofNatTrans (Functor.whiskerRight (NatTrans.op α) E)).limMap.comp
        (E.milnorObjToLimAdd htY) := by
  refine AddMonoidHom.ext fun u ↦ Subtype.ext <| funext fun n ↦ ?_
  have hcomm2 : ψ ≫ φ.hom₃ = φ.hom₂ ≫ ψ' := φ.comm₂
  have hcomm : (Sigma.ι X.obj n ≫ ψ) ≫ φ.hom₃ = α.app n ≫ Sigma.ι Y.obj n ≫ ψ' := by
    rw [Category.assoc, hcomm2, hφ₂, Sigma.ι_map_assoc]
  have hL : ((E.milnorObjToLimAdd htX).comp (E.map φ.hom₃.op).hom u :
      ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n =
      E.map (Sigma.ι X.obj n ≫ ψ).op (E.map φ.hom₃.op u) :=
    E.coe_milnorObjToLimAdd_apply htX (E.map φ.hom₃.op u) n
  have hR : ((Tower.Hom.ofNatTrans (Functor.whiskerRight (NatTrans.op α) E)).limMap.comp
      (E.milnorObjToLimAdd htY) u : ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n =
      E.map (α.app n).op (E.map (Sigma.ι Y.obj n ≫ ψ').op u) := by
    rw [AddMonoidHom.comp_apply, Tower.Hom.coe_limMap_apply, Tower.Hom.onProduct_apply,
      Tower.Hom.ofNatTrans_app, E.coe_milnorObjToLimAdd_apply htY u n]
    rfl
  exact hL.trans ((E.map_op_apply_eq_of_comp_eq hcomm u).trans hR.symm)

section Additive

variable [E.Additive]

/-- The connecting map `lim¹ E((Xₙ)⟦1⟧) →+ E(M)` of the Milnor exact sequence for an additive
functor `E : Tᵒᵖ ⥤ AddCommGrpCat`, valued on `CompactCoefficients.Tower.limOne`. -/
def milnorLimOneToObjAdd (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).limOne →+ E.obj (op M) :=
  ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht).toAddMonoidHom.comp
    (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).toAddMonoidHom

@[simp]
theorem milnorLimOneToObjAdd_mk (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    (x : ∀ n, (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).obj n) :
    E.milnorLimOneToObjAdd ht (QuotientAddGroup.mk x) =
      (E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht
        (Submodule.Quotient.mk fun n ↦
          (x n : ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E ⋙
            AddCommGrpCat.toIntModule.{s}).obj (op n))) := by
  have h1 : E.milnorLimOneToObjAdd ht (QuotientAddGroup.mk x) =
      (E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht
        (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)
          (QuotientAddGroup.mk x)) :=
    rfl
  exact h1.trans (congrArg _ (Tower.ofFunctorLimOneEquiv_mk _ x))

@[simp high]
theorem milnorLimOneToObjAdd_mk_map (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    (y : E.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    E.milnorLimOneToObjAdd ht
        (QuotientAddGroup.mk fun n ↦
          (E.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y :
            (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).obj n)) =
      E.map δ.op y := by
  have h1 := E.milnorLimOneToObjAdd_mk ht fun n ↦
    (E.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y :
      (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).obj n)
  exact h1.trans ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj_mk_map ht y)

/-- Naturality of the connecting map `lim¹ E((Xₙ)⟦1⟧) →+ E(M)` with respect to any morphism of
Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorLimOneToObjAdd_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n) :
    (E.map φ.hom₃.op).hom.comp (E.milnorLimOneToObjAdd htY) =
      (E.milnorLimOneToObjAdd htX).comp
        (Tower.Hom.ofNatTrans (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)).limOneMap := by
  refine AddMonoidHom.ext fun z ↦ ?_
  have h1 : (E.map φ.hom₃.op).hom (E.milnorLimOneToObjAdd htY z) =
      ((E ⋙ AddCommGrpCat.toIntModule.{s}).map φ.hom₃.op).hom
        ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj htY
          (Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E) z)) :=
    rfl
  have h2 : E.milnorLimOneToObjAdd htX
      ((Tower.Hom.ofNatTrans (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)).limOneMap z) =
      (E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj htX
        (ModuleTower.limOneMap (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ))))
            (E ⋙ AddCommGrpCat.toIntModule.{s}))
          (Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E) z)) :=
    congrArg ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj htX)
      (Tower.ofFunctorLimOneEquiv_limOneMap
        (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E) z)
  have hmod := LinearMap.congr_fun
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj_naturality htX htY α φ hφ₁)
    (Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E) z)
  exact h1.trans (hmod.trans h2.symm)

/-- The composite `lim¹ E((Xₙ)⟦1⟧) → E(M) → lim E(Xₙ)` of the `AddCommGrpCat`-valued Milnor
sequence is zero. -/
@[simp]
theorem milnorObjToLimAdd_comp_milnorLimOneToObjAdd
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorObjToLimAdd ht).comp (E.milnorLimOneToObjAdd ht) = 0 := by
  refine AddMonoidHom.ext fun z ↦ Subtype.ext <| funext fun n ↦ ?_
  have hmod := LinearMap.congr_fun
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim_comp_milnorLimOneToObj ht)
    (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E) z)
  have hcoord := congrArg
    (fun v : ModuleTower.lim (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule.{s}) ↦
      (v : ModuleTower.Product (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule.{s})) n) hmod
  have hL : ((E.milnorObjToLimAdd ht).comp (E.milnorLimOneToObjAdd ht) z :
      ∀ k, (Tower.ofFunctor (X.op ⋙ E)).obj k) n =
      ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht
        ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht
          (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E) z)) :
        ModuleTower.Product (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule.{s})) n :=
    Tower.coe_ofFunctorLimEquiv_symm_apply (X.op ⋙ E) _ n
  exact hL.trans hcoord

/-- The Milnor short complex `lim¹ E((Xₙ)⟦1⟧) ⟶ E(M) ⟶ lim E(Xₙ)` in `AddCommGrpCat`
attached to a Milnor homotopy colimit triangle. -/
@[expose]
def milnorShortComplexAdd (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    ShortComplex AddCommGrpCat.{s} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (E.milnorLimOneToObjAdd ht))
    (AddCommGrpCat.ofHom (E.milnorObjToLimAdd ht))
    (AddCommGrpCat.hom_ext (E.milnorObjToLimAdd_comp_milnorLimOneToObjAdd ht))

@[simp]
theorem milnorShortComplexAdd_X₁ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).X₁ =
      AddCommGrpCat.of (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).limOne :=
  rfl

@[simp]
theorem milnorShortComplexAdd_X₂ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).X₂ = E.obj (op M) :=
  rfl

@[simp]
theorem milnorShortComplexAdd_X₃ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).X₃ = AddCommGrpCat.of (Tower.ofFunctor (X.op ⋙ E)).lim :=
  rfl

@[simp]
theorem milnorShortComplexAdd_f (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).f = AddCommGrpCat.ofHom (E.milnorLimOneToObjAdd ht) :=
  rfl

@[simp]
theorem milnorShortComplexAdd_g (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).g = AddCommGrpCat.ofHom (E.milnorObjToLimAdd ht) :=
  rfl

/-- The contravariant morphism of `AddCommGrpCat`-valued Milnor short complexes
`E.milnorShortComplexAdd htY ⟶ E.milnorShortComplexAdd htX` induced by a morphism of Milnor
triangles `φ` extending a natural transformation `α : X ⟶ Y`. -/
@[expose]
def milnorShortComplexAddMap {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    E.milnorShortComplexAdd htY ⟶ E.milnorShortComplexAdd htX where
  τ₁ := AddCommGrpCat.ofHom (Tower.Hom.ofNatTrans (Functor.whiskerRight
    (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)).limOneMap
  τ₂ := E.map φ.hom₃.op
  τ₃ := AddCommGrpCat.ofHom
    (Tower.Hom.ofNatTrans (Functor.whiskerRight (NatTrans.op α) E)).limMap
  comm₁₂ := AddCommGrpCat.hom_ext (E.milnorLimOneToObjAdd_naturality htX htY α φ hφ₁).symm
  comm₂₃ := AddCommGrpCat.hom_ext (E.milnorObjToLimAdd_naturality htX htY α φ hφ₂)

@[simp]
theorem milnorShortComplexAddMap_τ₁ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (E.milnorShortComplexAddMap htX htY α φ hφ₁ hφ₂).τ₁ =
      AddCommGrpCat.ofHom (Tower.Hom.ofNatTrans (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)).limOneMap :=
  rfl

@[simp]
theorem milnorShortComplexAddMap_τ₂ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (E.milnorShortComplexAddMap htX htY α φ hφ₁ hφ₂).τ₂ = E.map φ.hom₃.op :=
  rfl

@[simp]
theorem milnorShortComplexAddMap_τ₃ {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    (E.milnorShortComplexAddMap htX htY α φ hφ₁ hφ₂).τ₃ =
      AddCommGrpCat.ofHom
        (Tower.Hom.ofNatTrans (Functor.whiskerRight (NatTrans.op α) E)).limMap :=
  rfl

/-- Comparison isomorphism in `ShortComplex AddCommGrpCat` identifying
`((E ⋙ AddCommGrpCat.toIntModule).milnorShortComplex ht).map (forget₂ (ModuleCat ℤ) AddCommGrpCat)`
with `E.milnorShortComplexAdd ht`. -/
@[expose]
def milnorShortComplexAddIso (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorShortComplex ht).map
        (forget₂ (ModuleCat.{s} ℤ) AddCommGrpCat.{s}) ≅
      E.milnorShortComplexAdd ht :=
  ShortComplex.isoMk
    (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).symm.toAddCommGrpIso
    (Iso.refl (E.obj (op M)))
    (Tower.ofFunctorLimEquiv (X.op ⋙ E)).symm.toAddCommGrpIso
    (AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun z ↦ by
      have h1 : ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht)
          ((Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E))
            ((Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).symm z)) =
          ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht) z :=
        congrArg ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht)
          ((Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).apply_symm_apply z)
      exact h1)
    (AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun u ↦ by
      change E.milnorObjToLimAdd ht u =
        (Tower.ofFunctorLimEquiv (X.op ⋙ E)).symm
          (((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht) u)
      rw [milnorObjToLimAdd]
      rfl)

/-- Naturality of the comparison isomorphism `milnorShortComplexAddIso` with respect to morphisms
of Milnor triangles extending `α : X ⟶ Y`. -/
theorem milnorShortComplexAddIso_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y.obj n)⟦(1 : ℤ)⟧)) E]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n)
    (hφ₂ : φ.hom₂ = Limits.Sigma.map fun n ↦ α.app n) :
    ((forget₂ (ModuleCat.{s} ℤ) AddCommGrpCat.{s}).mapShortComplex).map
        ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorShortComplexMap htX htY α φ hφ₁ hφ₂) ≫
      (E.milnorShortComplexAddIso htX).hom =
      (E.milnorShortComplexAddIso htY).hom ≫
        E.milnorShortComplexAddMap htX htY α φ hφ₁ hφ₂ := by
  ext1
  · refine AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun z ↦ ?_
    have hnat := Tower.ofFunctorLimOneEquiv_limOneMap
      (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)
      ((Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).symm z)
    have hinv :=
      (Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).apply_symm_apply z
    have hnat' : Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)
        ((Tower.Hom.ofNatTrans (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) E)).limOneMap
          ((Tower.ofFunctorLimOneEquiv ((Y ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).symm z)) =
        ModuleTower.limOneMap (Functor.whiskerRight
          (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ))))
            (E ⋙ AddCommGrpCat.toIntModule.{s})) z :=
      hnat.trans (congrArg _ hinv)
    exact (congrArg (Tower.ofFunctorLimOneEquiv _).symm hnat').symm.trans
      (by
        exact (Tower.ofFunctorLimOneEquiv _).symm_apply_apply _)
  · rfl
  · refine AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun u ↦ ?_
    have hnat := Tower.ofFunctorLimEquiv_limMap
      (Functor.whiskerRight (NatTrans.op α) E)
      ((Tower.ofFunctorLimEquiv (Y.op ⋙ E)).symm u)
    have hinv := (Tower.ofFunctorLimEquiv (Y.op ⋙ E)).apply_symm_apply u
    have hnat' : Tower.ofFunctorLimEquiv (X.op ⋙ E)
        ((Tower.Hom.ofNatTrans (Functor.whiskerRight (NatTrans.op α) E)).limMap
          ((Tower.ofFunctorLimEquiv (Y.op ⋙ E)).symm u)) =
        ModuleTower.limMap (Functor.whiskerRight (NatTrans.op α)
          (E ⋙ AddCommGrpCat.toIntModule.{s})) u :=
      hnat.trans (congrArg _ hinv)
    exact (congrArg (Tower.ofFunctorLimEquiv _).symm hnat').symm.trans
      ((Tower.ofFunctorLimEquiv _).symm_apply_apply _)

end Additive

section Homological

variable [E.IsHomological]

/-- The restriction map `E(M) →+ lim E(Xₙ)` of the `AddCommGrpCat`-valued Milnor sequence is
surjective. -/
theorem milnorObjToLimAdd_surjective
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) E] :
    Function.Surjective (E.milnorObjToLimAdd ht) :=
  (Tower.ofFunctorLimEquiv (X.op ⋙ E)).symm.surjective.comp
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim_surjective ht)

/-- The connecting map `lim¹ E((Xₙ)⟦1⟧) →+ E(M)` of the `AddCommGrpCat`-valued Milnor sequence
is injective. -/
theorem milnorLimOneToObjAdd_injective
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    Function.Injective (E.milnorLimOneToObjAdd ht) :=
  ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj_injective ht).comp
    (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).injective

/-- Exactness at the middle term of the `AddCommGrpCat`-valued Milnor sequence
`0 → lim¹ E((Xₙ)⟦1⟧) → E(M) → lim E(Xₙ) → 0`. -/
theorem exact_milnorLimOneToObjAdd_milnorObjToLimAdd
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    Function.Exact (E.milnorLimOneToObjAdd ht) (E.milnorObjToLimAdd ht) := by
  refine (Function.Exact.iff_of_ladder_addEquiv
    (Tower.ofFunctorLimOneEquiv ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E))
    (AddEquiv.refl (E.obj (op M)))
    (Tower.ofFunctorLimEquiv (X.op ⋙ E))
    (f₁₂ := E.milnorLimOneToObjAdd ht)
    (f₂₃ := E.milnorObjToLimAdd ht)
    (g₁₂ := ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorLimOneToObj ht).toAddMonoidHom)
    (g₂₃ := ((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht).toAddMonoidHom)
    (by
      rw [milnorLimOneToObjAdd]
      rfl)
    (AddMonoidHom.ext fun u ↦
      ((Tower.ofFunctorLimEquiv (X.op ⋙ E)).apply_symm_apply
        (((E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim ht) u)).symm)).1 ?_
  exact (E ⋙ AddCommGrpCat.toIntModule.{s}).exact_milnorLimOneToObj_milnorObjToLim ht

/-- The Milnor sequence `0 ⟶ lim¹ E((Xₙ)⟦1⟧) ⟶ E(M) ⟶ lim E(Xₙ) ⟶ 0` in `AddCommGrpCat` is
short exact for any contravariant homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat` preserving the
countable products of `X` and `X⟦1⟧`. -/
theorem shortExact_milnorShortComplexAdd
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E] :
    (E.milnorShortComplexAdd ht).ShortExact :=
  ShortComplex.shortExact_of_iso (E.milnorShortComplexAddIso ht) <|
    ((E ⋙ AddCommGrpCat.toIntModule.{s}).shortExact_milnorShortComplex ht).map_of_exact
      (forget₂ (ModuleCat.{s} ℤ) AddCommGrpCat.{s})

/-- When `lim¹ E((Xₙ)⟦1⟧)` vanishes, the Milnor restriction map `E(M) →+ lim E(Xₙ)` is
bijective. -/
theorem milnorObjToLimAdd_bijective_of_subsingleton_limOne
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) E]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X.obj n)⟦(1 : ℤ)⟧)) E]
    [Subsingleton (Tower.ofFunctor ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ E)).limOne] :
    Function.Bijective (E.milnorObjToLimAdd ht) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, E.milnorObjToLimAdd_surjective ht⟩
  obtain ⟨z, rfl⟩ := (E.exact_milnorLimOneToObjAdd_milnorObjToLimAdd ht u).1 hu
  rw [Subsingleton.elim z 0, map_zero]

end Homological

end AddCommGrpValued

end CategoryTheory.Functor

namespace TauCeti

section AddCommGrpValued

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- **Milnor lifting for `AddCommGrpCat`-valued cohomological functors:** for a contravariant
homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{s}` preserving the countable product of `X` and
any Milnor homotopy colimit triangle of `X : ℕ ⥤ T`, every compatible family
`x : ∀ n, E.obj (op (X.obj n))` lifts to an element `u : E.obj (op M)` restricting to `x n`
along each `Sigma.ι X.obj n ≫ ψ`. -/
theorem exists_lift_of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{s}) [E.IsHomological]
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) E]
    (x : ∀ n, E.obj (op (X.obj n)))
    (hx : ∀ n, E.map (X.map (homOfLE (Nat.le_add_right n 1))).op (x (n + 1)) = x n) :
    ∃ u : E.obj (op M), ∀ n, E.map (Sigma.ι X.obj n ≫ ψ).op u = x n := by
  obtain ⟨u, hu⟩ := E.milnorObjToLimAdd_surjective ht
    ⟨x, (CompactCoefficients.Tower.mem_lim (CompactCoefficients.Tower.ofFunctor (X.op ⋙ E))).2 hx⟩
  refine ⟨u, fun n ↦ ?_⟩
  have hcoord := congrArg
    (fun v : (CompactCoefficients.Tower.ofFunctor (X.op ⋙ E)).lim ↦
      (v : ∀ k, (CompactCoefficients.Tower.ofFunctor (X.op ⋙ E)).obj k) n) hu
  exact (E.coe_milnorObjToLimAdd_apply ht u n).symm.trans hcoord

end AddCommGrpValued

end TauCeti

end MilnorSequence
