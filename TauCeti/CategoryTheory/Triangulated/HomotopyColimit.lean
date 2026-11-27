/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Category.Grp.ZModuleEquivalence
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Compact
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.ModuleCat

import Mathlib.Algebra.Category.Grp.FilteredColimits
import TauCeti.CategoryTheory.ConcreteCategory.Basic
import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic
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
   natural short exact sequence, with `TauCeti.exists_lift_of_milnorTriangle` for
   `AddCommGrpCat`-valued functors.

## Main definitions

* `TauCeti.coconeOfMilnorTriangle`, `CategoryTheory.Functor.milnorObjToLim`,
  `CategoryTheory.Functor.milnorLimOneToObj`

## Main results

* `TauCeti.surjective_comp_of_milnorTriangle`, `TauCeti.isColimitMapCoconeOfMilnorTriangle`,
  `TauCeti.exists_factor_of_milnorTriangle`, `TauCeti.comp_ι_comp_eq_zero_iff_of_milnorTriangle`,
  `TauCeti.exists_lift_of_milnorTriangle`
* `CategoryTheory.Functor.milnorLimOneToObj_injective`,
  `CategoryTheory.Functor.exact_milnorLimOneToObj_milnorObjToLim`,
  `CategoryTheory.Functor.milnorObjToLim_surjective`,
  `CategoryTheory.Functor.milnorObjToLim_bijective_of_subsingleton_limOne`,
  `CategoryTheory.Functor.milnorObjToLim_naturality`,
  `CategoryTheory.Functor.milnorLimOneToObj_naturality`

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
  exact ((ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (op A)).map_distinguished_exact _ (rot_of_distTriang _ ht))) f hfδ

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
    rw [← Category.assoc, ← hcomp, Category.assoc, ← F.map_comp, hψ, F.map_zero, comp_zero]
  let iso : ∐ (X ⋙ F).obj ≅ F.obj (∐ X.obj) := asIso (sigmaComparison F X.obj)
  have hcok : IsColimit (CokernelCofork.ofπ (sigmaComparison F X.obj ≫ F.map ψ) hz) :=
    IsCokernel.ofIso _ hex.gIsCokernel _ iso.symm iso.symm (Iso.refl _)
      (by simp [iso, hcomp]) (by simp [iso])
  exact IsColimit.ofIsoColimit ((X ⋙ F).isColimitCoconeOfSequenceDifference hcok)
    (Cocone.ext (Iso.refl _) fun n ↦ by
      dsimp only [Functor.coconeOfSequenceDifference, Cofork.ofπ_pt, coconeOfMilnorTriangle]
      simp only [NatTrans.ofSequence_app, Cofork.π_ofπ, Iso.refl_hom, Category.comp_id,
        Functor.mapCocone_ι_app]
      exact (ι_comp_sigmaComparison_assoc F X.obj n (F.map ψ)).trans
        (F.map_comp (Sigma.ι X.obj n) ψ).symm)

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
  have hc := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{v})
    (isColimitMapCoconeOfMilnorTriangle ht (A := A))
  obtain ⟨N, h, hh⟩ := Types.jointly_surjective_of_isColimit hc g
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
      rw [Functor.mapCocone_ι_app, coconeOfMilnorTriangle_ι_app]
      exact hzero)
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
  simpa [-Functor.comp_obj] using F.map_op_apply_eq_of_comp_eq hcomm u

section Additive

variable [F.Additive]

private theorem map_δ_comp_cofanOpToPiLinearEquiv_symm_shift
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F] :
    ((F.map δ.op).hom ∘ₗ
        ((isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F).symm.toLinearMap) ∘ₗ
      ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) = 0 := by
  let e₁ := (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
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
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F] :
    ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F) →ₗ[R] F.obj (op M) :=
  let e₁ := (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  Submodule.liftQ (LinearMap.range (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F)))
    ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) <| by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (F.map_δ_comp_cofanOpToPiLinearEquiv_symm_shift ht) y

@[simp]
theorem milnorLimOneToObj_mk_map (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F]
    (y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧))) :
    F.milnorLimOneToObj ht
        (Submodule.Quotient.mk fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) =
      F.map δ.op y := by
  let e₁ := (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  have he₁ : (fun n ↦ F.map ((Sigma.ι X.obj n)⟦(1 : ℤ)⟧').op y) = e₁ y :=
    funext fun n ↦ ((isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv_apply F y n).symm
  rw [he₁]
  exact congrArg (F.map δ.op) (e₁.symm_apply_apply y)

/-- Naturality of the connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` with respect to any morphism
of Milnor triangles extending a morphism of sequences `α : X ⟶ Y`. -/
theorem milnorLimOneToObj_naturality {Y : ℕ ⥤ T} [HasCoproduct Y.obj] {M' : T}
    {ψ' : (∐ Y.obj) ⟶ M'} {δ' : M' ⟶ (∐ Y.obj)⟦(1 : ℤ)⟧}
    (htX : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (htY : Triangle.mk Y.sequenceDifference ψ' δ' ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((Y ⋙ shiftFunctor T (1 : ℤ)).obj n)) F]
    (α : X ⟶ Y)
    (φ : Triangle.mk X.sequenceDifference ψ δ ⟶ Triangle.mk Y.sequenceDifference ψ' δ')
    (hφ₁ : φ.hom₁ = Limits.Sigma.map fun n ↦ α.app n) :
    (F.map φ.hom₃.op).hom ∘ₗ F.milnorLimOneToObj htY = F.milnorLimOneToObj htX ∘ₗ
      ModuleTower.limOneMap (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight α (shiftFunctor T (1 : ℤ)))) F) := by
  let eY := (isColimitShiftedCoproductCofan Y).cofanOpToPiLinearEquiv F
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
    simpa [eY, -Functor.comp_obj, -Cofan.mk_pt] using (F.map_op_apply_eq_of_comp_eq hsq y).symm
  have hL : F.milnorLimOneToObj htY (Submodule.Quotient.mk (eY y)) = F.map δ'.op y :=
    congrArg (F.map δ'.op) (eY.symm_apply_apply y)
  simpa [hprod, hL] using (F.map_op_apply_eq_of_comp_eq φ.comm₃ y).symm

end Additive

section Homological

variable [F.IsHomological]

private theorem exact_op_milnor₁₂ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {x : F.obj (op (∐ X.obj))} (hx : F.map X.sequenceDifference.op x = 0) :
    ∃ u : F.obj (op M), F.map ψ.op u = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact _ ht) x hx

private theorem exact_op_milnor₂₃ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    {u : F.obj (op M)} (hu : F.map ψ.op u = 0) :
    ∃ y : F.obj (op ((∐ X.obj)⟦(1 : ℤ)⟧)), F.map δ.op y = u :=
  (ShortComplex.moduleCat_exact_iff _).1
    (F.map_distinguished_op_exact _ (rot_of_distTriang _ ht)) u hu

private theorem exact_op_milnor₃₁ (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T) :
    Function.Exact (F.map ((X.sequenceDifference)⟦(1 : ℤ)⟧').op).hom (F.map δ.op).hom := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (F.map_distinguished_op_exact _ (rot_of_distTriang _ (rot_of_distTriang _ ht)))
  exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.neg R)
    (e₂ := LinearEquiv.refl R _) (e₃ := LinearEquiv.refl R _)
    (LinearMap.ext fun x ↦ by simp [op_neg, F.map_neg]) (LinearMap.ext fun _ ↦ rfl) hex

/-- The restriction map `F(M) →ₗ[R] lim F(Xₙ)` of the Milnor sequence is surjective. -/
theorem milnorObjToLim_surjective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F] :
    Function.Surjective (F.milnorObjToLim ht) := fun ⟨x, hx⟩ ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  have hzero : F.map X.sequenceDifference.op (e.symm x) = 0 := e.injective <| by
    rw [cofanOpToPiLinearEquiv_map_sequenceDifference, LinearEquiv.apply_symm_apply, map_zero]
    exact LinearMap.mem_ker.1 (ModuleTower.lim_eq_ker (X.op ⋙ F) ▸ hx)
  obtain ⟨u, hu⟩ := exact_op_milnor₁₂ F ht hzero
  refine ⟨u, Subtype.ext <| funext fun n ↦ ?_⟩
  rw [coe_milnorObjToLim_apply, map_op_comp_apply, hu]
  exact (coproductIsCoproduct X.obj).map_inj_cofanOpToPiLinearEquiv_symm F x n

/-- The connecting map `lim¹ F((Xₙ)⟦1⟧) →ₗ[R] F(M)` of the Milnor sequence is
injective. -/
theorem milnorLimOneToObj_injective (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F] :
    Function.Injective (F.milnorLimOneToObj ht) := by
  let e₁ := (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  have hex : Function.Exact (ModuleTower.shift ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))
      ((F.map δ.op).hom ∘ₗ e₁.symm.toLinearMap) :=
    Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e₁) (e₂ := e₁)
      (e₃ := LinearEquiv.refl R _)
      (LinearMap.ext fun x ↦ (cofanOpToPiLinearEquiv_map_shift_sequenceDifference F X x).symm)
      (LinearMap.ext fun _ ↦ by simp) (exact_op_milnor₃₁ F ht)
  exact LinearMap.injective_range_liftQ_of_exact hex

/-- Exactness at the middle term of the Milnor sequence
`0 → lim¹ F((Xₙ)⟦1⟧) → F(M) → lim F(Xₙ) → 0`. -/
theorem exact_milnorLimOneToObj_milnorObjToLim
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F] :
    Function.Exact (F.milnorLimOneToObj ht) (F.milnorObjToLim ht) := fun u ↦ by
  let e := (coproductIsCoproduct X.obj).cofanOpToPiLinearEquiv F
  let e₁ := (isColimitShiftedCoproductCofan X).cofanOpToPiLinearEquiv F
  refine ⟨fun hu ↦ ?_, ?_⟩
  · have hψ : F.map ψ.op u = 0 := e.injective <| by
      rw [map_zero]; funext n
      have hcoord := congrArg
        (fun v : ModuleTower.lim (X.op ⋙ F) ↦ (v : ModuleTower.Product (X.op ⋙ F)) n) hu
      rw [coe_milnorObjToLim_apply, map_op_comp_apply] at hcoord
      dsimp only [e]; rw [IsColimit.cofanOpToPiLinearEquiv_apply]; exact hcoord
    obtain ⟨y, hy⟩ := exact_op_milnor₂₃ F ht hψ
    exact ⟨Submodule.Quotient.mk (e₁ y), (congrArg (F.map δ.op) (e₁.symm_apply_apply y)).trans hy⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hψδ : ψ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ ht
    ext n
    simp only [ModuleTower.limπ_apply, coe_milnorObjToLim_apply, milnorLimOneToObj,
      Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ZeroMemClass.coe_zero, Pi.zero_apply]
    rw [← map_op_comp_apply, Category.assoc, hψδ, comp_zero, op_zero, F.map_zero]
    simp

/-- When `lim¹ F((Xₙ)⟦1⟧)` vanishes, the Milnor restriction map `F(M) →ₗ[R] lim F(Xₙ)`
is bijective. -/
theorem milnorObjToLim_bijective_of_subsingleton_limOne
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    [PreservesLimit (Discrete.functor fun n ↦ op (X.obj n)) F]
    [PreservesLimit (Discrete.functor fun n ↦ op ((X ⋙ shiftFunctor T (1 : ℤ)).obj n)) F]
    [Subsingleton (ModuleTower.limOne ((X ⋙ shiftFunctor T (1 : ℤ)).op ⋙ F))] :
    Function.Bijective (F.milnorObjToLim ht) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, F.milnorObjToLim_surjective ht⟩
  obtain ⟨z, rfl⟩ := (F.exact_milnorLimOneToObj_milnorObjToLim ht u).1 hu
  rw [Subsingleton.elim z 0, map_zero]

end Homological

end ModuleValued

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
  obtain ⟨u, hu⟩ := (E ⋙ AddCommGrpCat.toIntModule.{s}).milnorObjToLim_surjective ht
    ⟨x, (ModuleTower.mem_lim (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule.{s})).2 fun n ↦ by
      rw [ModuleTower.transition_def, Functor.comp_map, Functor.comp_map,
        AddCommGrpCat.toIntModule_map_apply]
      exact hx n⟩
  refine ⟨u, fun n ↦ ?_⟩
  have hcoord := congrArg
    (fun v : ModuleTower.lim (X.op ⋙ E ⋙ AddCommGrpCat.toIntModule.{s}) ↦ v.val n) hu
  rw [(E ⋙ AddCommGrpCat.toIntModule.{s}).coe_milnorObjToLim_apply ht u n,
    Functor.comp_map] at hcoord
  exact (AddCommGrpCat.toIntModule_map_apply (E.map (Sigma.ι X.obj n ≫ ψ).op) u).symm.trans hcoord

end AddCommGrpValued

end TauCeti

end MilnorSequence
