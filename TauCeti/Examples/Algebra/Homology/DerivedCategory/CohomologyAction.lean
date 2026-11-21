/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.Homology.DerivedCategory.CohomologyAction
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.Homology.DerivedCategory.SingleTriangle
import TauCeti.CategoryTheory.Preadditive.NSMul
import TauCeti.Data.ZMod.MulCastHom

/-!
# Examples: cohomology actions and ghost ideals in the derived category

These examples exercise `TauCeti.Algebra.Homology.DerivedCategory.CohomologyAction` on concrete
objects in `DerivedCategory (ModuleCat ℤ)`:

* the general quotient isomorphism
  `α.range ⧸ α.imageGhostIdeal ≃ₐ[A] ((X.cohomologyAction A).comp α).range`;
* the zero object `0`, where every endomorphism is a ghost (`actionGhostKer = ⊤`,
  `imageGhostIdeal = ⊤`) while `ghostIdeal = ⊥` in the trivial endomorphism ring;
* `ℤ[0]` with scalar action `ℤ →ₐ[ℤ] End ℤ[0]` (zero ghost ideal, faithful cohomology action) and
  with `Polynomial ℤ →ₐ[ℤ] End ℤ[0]` via evaluation at `0` (`actionGhostKer = (X)` while
  `imageGhostIdeal = ⊥`);
* `(ℤ × ℤ)[0]` with noncommuting endomorphisms `E₀₁, E₁₀`, distinguishing `E₀₁ * E₁₀` from
  `E₁₀ * E₀₁` on `H^0`;
* `TauCeti.Examples.CohomologyAction.exists_nonzero_sq_zero_ghost`: `(ℤ/2)[0] ⊞ (ℤ/2)[1]` admits a
  nonzero square-zero ghost constructed from the non-split extension
  `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`, giving `RingHom.ker α = (2, X^2)` strictly contained in
  `actionGhostKer α = (2, X)`, a nonzero square-zero `α.imageGhostIdeal`, and a nontrivial
  quotient `α.imageGhostIdealQuotientEquivCohomologyImage`.
-/

public section

open CategoryTheory Limits Pretriangulated Triangulated DerivedCategory TauCeti.DerivedCategory
open ZeroObject

namespace TauCeti.Examples.CohomologyAction

universe t' t w v u

example {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C] [Linear A C]
    [HasDerivedCategory.{t} C] {H : Type t'} [Semiring H] [Algebra A H]
    (X : DerivedCategory C) (α : H →ₐ[A] End X) :
    Nonempty ((α.range ⧸ α.imageGhostIdeal) ≃ₐ[A] ((X.cohomologyAction A).comp α).range) :=
  ⟨α.imageGhostIdealQuotientEquivCohomologyImage⟩

attribute [local instance] HasDerivedCategory.standard

example :
    let X : DerivedCategory (ModuleCat.{0} ℤ) := 0
    let α : ℤ →ₐ[ℤ] End X := Algebra.ofId ℤ (End X)
    X.cohomologyAction ℤ (algebraMap ℤ (End X) 7) = 0 ∧
    X.ghostIdeal = ⊥ ∧
    actionGhostKer α = ⊤ ∧
    α.imageGhostIdeal = ⊤ ∧
    α.imageGhostIdealQuotientEquivCohomologyImage
      (Ideal.Quotient.mk _ (α.rangeRestrict 7)) = 0 := by
  intro X α
  have hX : IsZero X := isZero_zero _
  have hEnd : Subsingleton (End X) :=
    ⟨fun f g ↦ End.ext ((hX.eq_of_src f.asHom 0).trans (hX.eq_of_src g.asHom 0).symm)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    apply End.ext
    exact ((homologyFunctor (ModuleCat.{0} ℤ) i).map_isZero hX).eq_of_src _ _
  · ext f
    simp [Subsingleton.elim f 0]
  · ext r
    simp only [mem_actionGhostKer_iff, Submodule.mem_top, iff_true]
    rw [Subsingleton.elim (α r) 0]
    exact End.isGhost_zero
  · ext x
    simp [Subsingleton.elim x.1 0]
  · apply Subtype.ext
    funext i
    apply End.ext
    exact ((homologyFunctor (ModuleCat.{0} ℤ) i).map_isZero hX).eq_of_src _ _

example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    let α : ℤ →ₐ[ℤ] End X := Algebra.ofId ℤ (End X)
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ ModuleCat.of ℤ ℤ :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)
    e.hom ((X.cohomologyAction ℤ (algebraMap ℤ (End X) 2) 0).asHom (e.inv 3)) = (6 : ℤ) ∧
    X.ghostIdeal = ⊥ ∧
    actionGhostKer α = ⊥ ∧
    α.imageGhostIdeal = ⊥ ∧
    e.hom (((α.imageGhostIdealQuotientEquivCohomologyImage
      (Ideal.Quotient.mk _ (α.rangeRestrict 2))).1 0).asHom (e.inv 3)) = (6 : ℤ) := by
  intro X α e
  have hscalar : ∀ n : ℤ,
      e.hom ((X.cohomologyAction ℤ (algebraMap ℤ (End X) n) 0).asHom (e.inv 3)) = n * 3 := by
    intro n
    have h1 : (X.cohomologyAction ℤ (algebraMap ℤ (End X) n) 0).asHom =
        n • 𝟙 ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X) := by
      simp [End.intCast_asHom]
    rw [h1]
    simp [Iso.inv_hom_id_apply]
  have hghost0 : ∀ f : End X, f.IsGhost → f = 0 := fun f hf ↦
    End.ext <| (homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE f.asHom 0).mp
      (End.isGhost_iff.mp hf 0)
  have halg_inj : Function.Injective (algebraMap ℤ (End X)) := by
    intro a b hab
    have h := congrArg (fun g ↦ e.hom ((X.cohomologyAction ℤ g 0).asHom (e.inv 3))) hab
    have h' : a * 3 = b * 3 := by simpa only [hscalar] using h
    omega
  refine ⟨(hscalar 2).trans (by decide), ?_, ?_, ?_, ?_⟩
  · ext f
    simp only [mem_ghostIdeal_iff, TwoSidedIdeal.mem_bot]
    exact ⟨hghost0 f, fun h ↦ by simp [h]⟩
  · ext n
    simp only [mem_actionGhostKer_iff, Ideal.mem_bot]
    exact ⟨fun h ↦ halg_inj (by simpa [α] using hghost0 _ h), fun h ↦ by simp [h]⟩
  · ext x
    simp only [AlgHom.mem_imageGhostIdeal_iff, Ideal.mem_bot]
    exact ⟨fun h ↦ Subtype.ext (hghost0 x.1 h), fun h ↦ by simp [h]⟩
  · rw [AlgHom.imageGhostIdealQuotientEquivCohomologyImage_mk_val]
    exact (hscalar 2).trans (by decide)

example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    let α : Polynomial ℤ →ₐ[ℤ] End X :=
      (Algebra.ofId ℤ (End X)).comp (Polynomial.aeval (0 : ℤ))
    actionGhostKer α = Ideal.span {Polynomial.X} ∧ α.imageGhostIdeal = ⊥ := by
  intro X α
  have hghost0 : ∀ f : End X, f.IsGhost → f = 0 := fun f hf ↦
    End.ext <| (homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE f.asHom 0).mp
      (End.isGhost_iff.mp hf 0)
  have hscalar : ∀ n : ℤ, algebraMap ℤ (End X) n = 0 → n = 0 := by
    intro n hn
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ ModuleCat.of ℤ ℤ :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)
    have h1 : (X.cohomologyAction ℤ (algebraMap ℤ (End X) n) 0).asHom = 0 := by simp [hn]
    simp only [cohomologyAction_apply_asHom, End.algebraMap_asHom, Functor.map_zsmul,
      CategoryTheory.Functor.map_id] at h1
    have h3 : e.hom ((n • 𝟙 ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X)).hom (e.inv 1)) = 0 := by
      simp [h1]
    simpa [Iso.inv_hom_id_apply] using h3
  have hαp : ∀ p : Polynomial ℤ, α p = algebraMap ℤ (End X) (p.coeff 0) := by
    intro p
    simp [α, Polynomial.coeff_zero_eq_eval_zero]
  constructor
  · ext p
    rw [mem_actionGhostKer_iff, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    constructor
    · intro hp
      exact hscalar (p.coeff 0) (by rw [← hαp p]; exact hghost0 _ hp)
    · intro hp
      rw [hαp p, hp, map_zero]
      exact End.isGhost_zero
  · ext x
    simp only [AlgHom.mem_imageGhostIdeal_iff, Ideal.mem_bot]
    exact ⟨fun h ↦ Subtype.ext (hghost0 x.1 h), fun h ↦ by simp [h]⟩

example :
    let V := ModuleCat.of ℤ (ℤ × ℤ)
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj V
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ V :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app V
    let f₀₁ : V ⟶ V := ModuleCat.ofHom
      { toFun := fun p ↦ (p.2, 0), map_add' := fun _ _ ↦ by simp, map_smul' := fun _ _ ↦ by simp }
    let f₁₀ : V ⟶ V := ModuleCat.ofHom
      { toFun := fun p ↦ (0, p.1), map_add' := fun _ _ ↦ by simp, map_smul' := fun _ _ ↦ by simp }
    let E₀₁ : End X := End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f₀₁)
    let E₁₀ : End X := End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f₁₀)
    e.hom ((X.cohomologyAction ℤ (E₀₁ * E₁₀) 0).asHom (e.inv (2, 3))) = (2, 0) ∧
    e.hom ((X.cohomologyAction ℤ (E₁₀ * E₀₁) 0).asHom (e.inv (2, 3))) = (0, 3) := by
  intro V X e f₀₁ f₁₀ E₀₁ E₁₀
  have hnat : ∀ f : V ⟶ V,
      e.hom ((X.cohomologyAction ℤ (End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f)) 0).asHom
        (e.inv (2, 3))) = f (2, 3) := by
    intro f
    have h : (homologyFunctor (ModuleCat.{0} ℤ) 0).map ((singleFunctor (ModuleCat.{0} ℤ) 0).map f) ≫
        e.hom = e.hom ≫ f :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).hom.naturality f
    have h' : e.inv ≫ (homologyFunctor (ModuleCat.{0} ℤ) 0).map
        ((singleFunctor (ModuleCat.{0} ℤ) 0).map f) ≫ e.hom = f := by
      rw [h, Iso.inv_hom_id_assoc]
    have hval := congrArg (fun g : V ⟶ V ↦ g (2, 3)) h'
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hval
    simpa [cohomologyAction_apply_asHom] using hval
  constructor
  · have hmul : E₀₁ * E₁₀ = End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map (f₁₀ ≫ f₀₁)) := by
      simp [E₀₁, E₁₀]
    rw [hmul, hnat]
    simp [f₀₁, f₁₀]
  · have hmul : E₁₀ * E₀₁ = End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map (f₀₁ ≫ f₁₀)) := by
      simp [E₀₁, E₁₀]
    rw [hmul, hnat]
    simp [f₀₁, f₁₀]

private abbrev zmod2ShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk
    (ModuleCat.ofHom (ZMod.mulCastHom 2 (rfl : 2 * 2 = 4)).toIntLinearMap)
    (ModuleCat.ofHom (ZMod.castHom (Dvd.intro_left 2 rfl) (ZMod 2)).toIntLinearMap)
    (by
      ext (x : ZMod 2)
      exact ZMod.castHom_mulCastHom 2 (rfl : 2 * 2 = 4) x)

private theorem zmod2ShortComplex_shortExact : zmod2ShortComplex.ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : ZMod 4) hx
    exact (ZMod.exact_mulCastHom_castHom 2 (rfl : 2 * 2 = 4) x).mp hx
  mono_f :=
    (ModuleCat.mono_iff_injective _).mpr (ZMod.mulCastHom_injective 2 (rfl : 2 * 2 = 4) two_ne_zero)
  epi_g :=
    (ModuleCat.epi_iff_surjective _).mpr
      (ZMod.castHom_surjective (n := 4) (m := 2) (Dvd.intro_left 2 rfl))

private theorem zmod2ShortComplex_not_isSplitEpi : ¬ IsSplitEpi zmod2ShortComplex.g := by
  rintro ⟨⟨s, hs⟩⟩
  have h1 : zmod2ShortComplex.g (s (1 : ZMod 2)) = (1 : ZMod 2) := by
    have h := congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ ModuleCat.of ℤ (ZMod 2) ↦ f 1) hs
    simpa [ModuleCat.comp_apply] using h
  have h2 : (2 : ℤ) • (s (1 : ZMod 2) : ZMod 4) = 0 := by
    have hsmul : s.hom ((2 : ℤ) • (1 : ZMod 2)) = (2 : ℤ) • s.hom (1 : ZMod 2) :=
      map_zsmul s.hom (2 : ℤ) (1 : ZMod 2)
    rw [← hsmul, show (2 : ℤ) • (1 : ZMod 2) = 0 by decide, map_zero]
  generalize hx : (s (1 : ZMod 2) : ZMod 4) = x at h1 h2
  fin_cases x
  · exact (by decide : (0 : ZMod 2) ≠ 1) h1
  · exact (by decide : (2 : ℤ) • (1 : ZMod 4) ≠ 0) h2
  · exact (by decide : (0 : ZMod 2) ≠ 1) h1
  · exact (by decide : (2 : ℤ) • (3 : ZMod 4) ≠ 0) h2

private noncomputable def zmod2Ext1Map :
    (singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2)) ⟶
      (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)) :=
  ((singleFunctors (ModuleCat.{0} ℤ)).shiftIso (-1) 1 0 (by omega)).inv.app _ ≫
    zmod2ShortComplex_shortExact.singleδ⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ) (by omega)).hom.app
      ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))

private theorem zmod2Ext1Map_ne_zero : zmod2Ext1Map ≠ 0 := by
  intro h0
  have hδ₀ : zmod2ShortComplex_shortExact.singleδ ≠ 0 := by
    rw [ne_eq, ShortComplex.ShortExact.singleδ_eq_zero_iff]
    exact zmod2ShortComplex_not_isSplitEpi
  apply hδ₀
  apply (shiftFunctor (DerivedCategory (ModuleCat.{0} ℤ)) (-1 : ℤ)).map_injective
  rw [Functor.map_zero]
  have h1 : zmod2ShortComplex_shortExact.singleδ⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ)
        (by omega)).hom.app ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) =
      0 := by
    rw [← cancel_epi (((singleFunctors (ModuleCat.{0} ℤ)).shiftIso (-1) 1 0 (by omega)).inv.app _)]
    simpa [zmod2Ext1Map, Category.assoc] using h0
  exact (cancel_mono ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ)
    (by omega)).hom.app _)).mp (by rw [zero_comp]; exact h1)

private noncomputable abbrev zmod2M : DerivedCategory (ModuleCat.{0} ℤ) :=
  (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)) ⊞
    (singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2))

private noncomputable abbrev zmod2Ghost : End zmod2M :=
  End.of (biprod.snd ≫ zmod2Ext1Map ≫ biprod.inl)

private noncomputable abbrev zmod2Action : Polynomial ℤ →ₐ[ℤ] End zmod2M :=
  Polynomial.aeval zmod2Ghost

private theorem zmod2_biprod_isGE_isLE : zmod2M.IsGE 0 ∧ zmod2M.IsLE 1 := by
  let T : Triangle (DerivedCategory (ModuleCat.{0} ℤ)) := binaryBiproductTriangle
    ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))
    ((singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2)))
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{0} ℤ)) :=
    Pretriangulated.binaryBiproductTriangle_distinguished _ _
  have hge₁ : TStructure.t.IsGE T.obj₁ 0 := by
    rw [binaryBiproductTriangle_obj₁]; infer_instance
  have hge₃ : TStructure.t.IsGE T.obj₃ 0 := by
    rw [binaryBiproductTriangle_obj₃]; exact TStructure.t.isGE_of_ge _ 0 1 (by omega)
  have hle₁ : TStructure.t.IsLE T.obj₁ 1 := by
    rw [binaryBiproductTriangle_obj₁]; exact TStructure.t.isLE_of_le _ 0 1 (by omega)
  have hle₃ : TStructure.t.IsLE T.obj₃ 1 := by
    rw [binaryBiproductTriangle_obj₃]; infer_instance
  exact ⟨by simpa only [T, binaryBiproductTriangle_obj₂] using TStructure.t.isGE₂ T hT 0 hge₁ hge₃,
    by simpa only [T, binaryBiproductTriangle_obj₂] using TStructure.t.isLE₂ T hT 1 hle₁ hle₃⟩

private theorem zmod2_two_smul_id_eq_zero :
    (2 : ℤ) • (1 : End zmod2M) = 0 ∧ (2 : ℤ) • zmod2Ext1Map = 0 ∧
      (2 : ℤ) • 𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) = 0 ∧
      𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) ≠ 0 := by
  have h2F₂ : (2 : ℤ) • 𝟙 (ModuleCat.of ℤ (ZMod 2)) = 0 := by
    ext (a : ZMod 2); fin_cases a <;> decide
  have h2s : ∀ n : ℤ,
      (2 : ℤ) • 𝟙 ((singleFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ZMod 2))) = 0 := by
    intro n
    rw [← (singleFunctor (ModuleCat.{0} ℤ) n).map_id,
      ← (singleFunctor (ModuleCat.{0} ℤ) n).map_zsmul, h2F₂, Functor.map_zero]
  have hcomp : ∀ {X Y : DerivedCategory (ModuleCat.{0} ℤ)} (f : X ⟶ Y),
      (2 : ℤ) • 𝟙 X = 0 → (2 : ℤ) • f = 0 := fun f h ↦ by
    rw [← Category.id_comp f, ← Preadditive.zsmul_comp, h, zero_comp]
  refine ⟨?_, ?_, h2s 0, ?_⟩
  · apply End.ext
    rw [End.smul_asHom, End.one_asHom, End.zero_asHom]
    apply biprod.hom_ext'
    · simpa [Preadditive.comp_zsmul] using hcomp biprod.inl (h2s 0)
    · simpa [Preadditive.comp_zsmul] using hcomp biprod.inr (h2s 1)
  · exact hcomp zmod2Ext1Map (h2s 1)
  · intro h
    have hF₂ : 𝟙 (ModuleCat.of ℤ (ZMod 2)) = 0 :=
      (singleFunctor (ModuleCat.{0} ℤ) 0).map_injective (by simpa using h)
    exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ _ ↦ f 1) hF₂)

private theorem zmod2_ghost_sq : zmod2Ghost ^ 2 = 0 :=
  End.ext (by simp [sq, Category.assoc])

private theorem zmod2Action_apply (p : Polynomial ℤ) :
    zmod2Action p = (p.coeff 0 : ℤ) • 1 + (p.coeff 1 : ℤ) • zmod2Ghost := by
  have h1 : p = Polynomial.X * p.divX + Polynomial.C (p.coeff 0) :=
    (Polynomial.X_mul_divX_add p).symm
  have h2 : p.divX = Polynomial.X * p.divX.divX + Polynomial.C (p.coeff 1) := by
    simpa [Polynomial.coeff_divX] using (Polynomial.X_mul_divX_add p.divX).symm
  conv_lhs => rw [h1, h2]
  simp [zmod2Action, mul_add, ← mul_assoc, ← sq, zmod2_ghost_sq, Int.cast_comm, add_comm]

private theorem zmod2_ghost_ker :
    RingHom.ker zmod2Action = Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} := by
  have ⟨h2M, h2δ, h2s0, hid0⟩ := zmod2_two_smul_id_eq_zero
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord0 :
      addOrderOf (𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))) = 2 :=
    addOrderOf_eq_prime (by simpa [← natCast_zsmul] using h2s0) hid0
  have hordδ : addOrderOf zmod2Ext1Map = 2 :=
    addOrderOf_eq_prime (by simpa [← natCast_zsmul] using h2δ) zmod2Ext1Map_ne_zero
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
  · have hp0 : (p.coeff 0 : ℤ) • (1 : End zmod2M) + (p.coeff 1 : ℤ) • zmod2Ghost = 0 := by
      simpa [zmod2Action_apply] using hp
    obtain ⟨k₀, hk₀⟩ : (2 : ℤ) ∣ p.coeff 0 := by
      have hcomp := congrArg (fun g : End zmod2M ↦ biprod.inl ≫ g.asHom ≫ biprod.fst) hp0
      have h0 : (p.coeff 0 : ℤ) •
          𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) = 0 := by
        simpa [End.intCast_asHom, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
          Category.assoc] using hcomp
      simpa [hord0] using (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h0
    obtain ⟨k₁, hk₁⟩ : (2 : ℤ) ∣ p.coeff 1 := by
      have hcomp := congrArg (fun g : End zmod2M ↦ biprod.inr ≫ g.asHom ≫ biprod.fst) hp0
      have h1 : (p.coeff 1 : ℤ) • zmod2Ext1Map = 0 := by
        simpa [End.intCast_asHom, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
          Category.assoc] using hcomp
      simpa [hordδ] using (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h1
    have hp_eq : p = Polynomial.C (2 * k₀) + Polynomial.C (2 * k₁) * Polynomial.X +
        Polynomial.X ^ 2 * p.divX.divX := by
      have h1 := (Polynomial.X_mul_divX_add p).symm
      have h2 : p.divX = Polynomial.X * p.divX.divX + Polynomial.C (p.coeff 1) := by
        simpa [Polynomial.coeff_divX] using (Polynomial.X_mul_divX_add p.divX).symm
      conv_lhs => rw [h1, h2, hk₀, hk₁]
      ring
    have h2mem : (2 : Polynomial ℤ) ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} :=
      Ideal.subset_span (by simp)
    have hX2mem : Polynomial.X ^ 2 ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} :=
      Ideal.subset_span (by simp)
    rw [hp_eq]
    exact Ideal.add_mem _
      (Ideal.add_mem _ (by simpa [mul_comm] using Ideal.mul_mem_left _ (Polynomial.C k₀) h2mem)
        (Ideal.mul_mem_right _ _
          (by simpa [mul_comm] using Ideal.mul_mem_left _ (Polynomial.C k₁) h2mem)))
      (Ideal.mul_mem_right _ _ hX2mem)
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_ofNat]
      simpa [zsmul_one] using h2M
    · simp [RingHom.mem_ker, zmod2_ghost_sq]

private theorem zmod2_action_ghost_ker :
    zmod2Ghost.IsGhost ∧
      actionGhostKer zmod2Action = Ideal.span {(2 : Polynomial ℤ), Polynomial.X} := by
  have ⟨h2M, _, h2s0, hid0⟩ := zmod2_two_smul_id_eq_zero
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord0 :
      addOrderOf (𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))) = 2 :=
    addOrderOf_eq_prime (by simpa [← natCast_zsmul] using h2s0) hid0
  have hghostx : zmod2Ghost.IsGhost := End.isGhost_iff.mpr fun i ↦ by
    have hδi : (homologyFunctor (ModuleCat.{0} ℤ) i).map zmod2Ext1Map = 0 := by
      rcases lt_or_ge i 1 with hlt | hge'
      · exact (isZero_of_isGE _ 1 i hlt).eq_of_src _ _
      · exact (isZero_of_isLE _ 0 i (by omega)).eq_of_tgt _ _
    simp [hδi]
  refine ⟨hghostx, le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)⟩
  · have hp0 : zmod2M.cohomologyAction ℤ (zmod2Action p) = 0 :=
      (End.isGhost_iff_cohomologyAction_eq_zero ℤ).mp (mem_actionGhostKer_iff.mp hp)
    have hcohx : zmod2M.cohomologyAction ℤ zmod2Ghost = 0 :=
      (End.isGhost_iff_cohomologyAction_eq_zero ℤ).mp hghostx
    have h0 : (p.coeff 0 : ℤ) •
        𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) = 0 := by
      have hcomp := congrArg (fun g ↦ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.inl ≫
        (g 0).asHom ≫ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.fst) hp0
      rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ 0]
      simpa [zmod2Action_apply, hcohx, End.intCast_asHom, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp, ← Functor.map_comp] using hcomp
    obtain ⟨k₀, hk₀⟩ : (2 : ℤ) ∣ p.coeff 0 :=
      by simpa [hord0] using (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h0
    have hpX : p = Polynomial.C (2 * k₀) + Polynomial.X * p.divX := by
      rw [← hk₀, add_comm]
      exact (Polynomial.X_mul_divX_add p).symm
    have h2mem : (2 : Polynomial ℤ) ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X} :=
      Ideal.subset_span (by simp)
    have hXmem : Polynomial.X ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X} :=
      Ideal.subset_span (by simp)
    rw [hpX]
    exact Ideal.add_mem _
      (by simpa [mul_comm] using Ideal.mul_mem_left _ (Polynomial.C k₀) h2mem)
      (Ideal.mul_mem_right _ _ hXmem)
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [SetLike.mem_coe, mem_actionGhostKer_iff]
      have h2 : zmod2Action 2 = 0 := by rw [map_ofNat]; simpa [zsmul_one] using h2M
      rw [h2]
      exact End.isGhost_zero
    · simpa [mem_actionGhostKer_iff] using hghostx

/-- There exists an object `X` in `DerivedCategory (ModuleCat ℤ)` concentrated in `[0, 1]` and an
algebra action `α : Polynomial ℤ →ₐ[ℤ] End X` whose image ghost ideal is nonzero and square-zero,
with `RingHom.ker α = (2, X^2)` strictly contained in `actionGhostKer α = (2, X)` and a nontrivial
quotient `α.imageGhostIdealQuotientEquivCohomologyImage`. -/
theorem exists_nonzero_sq_zero_ghost :
    ∃ (X : DerivedCategory (ModuleCat.{0} ℤ)) (α : Polynomial ℤ →ₐ[ℤ] End X) (g : End X),
      X.IsGE 0 ∧ X.IsLE 1 ∧
      g ≠ 0 ∧ g ^ 2 = 0 ∧
      X.cohomologyAction ℤ g = 0 ∧ g ∈ X.ghostIdeal ∧
      RingHom.ker α = Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} ∧
      actionGhostKer α = Ideal.span {(2 : Polynomial ℤ), Polynomial.X} ∧
      α.rangeRestrict Polynomial.X ∈ α.imageGhostIdeal ∧
      α.rangeRestrict Polynomial.X ≠ 0 ∧ α.imageGhostIdeal ^ 2 = ⊥ ∧
      α.imageGhostIdealQuotientEquivCohomologyImage
        (Ideal.Quotient.mk _ (α.rangeRestrict Polynomial.X)) = 0 ∧
      α.imageGhostIdealQuotientEquivCohomologyImage
        (Ideal.Quotient.mk _ (α.rangeRestrict 1)) ≠ 0 := by
  have ⟨hge, hle⟩ := zmod2_biprod_isGE_isLE
  have ⟨_, _, _, hid0⟩ := zmod2_two_smul_id_eq_zero
  have ⟨hghostx, hghostker⟩ := zmod2_action_ghost_ker
  have hUR : biprod.inr ≫ zmod2Ghost.asHom ≫ biprod.fst = zmod2Ext1Map := by
    simp [Category.assoc]
  have hxne : zmod2Ghost ≠ 0 := fun h ↦ zmod2Ext1Map_ne_zero (by rw [← hUR, h]; simp)
  have hcohx : zmod2M.cohomologyAction ℤ zmod2Ghost = 0 :=
    (End.isGhost_iff_cohomologyAction_eq_zero ℤ).mp hghostx
  have h1ne : zmod2Action.imageGhostIdealQuotientEquivCohomologyImage
      (Ideal.Quotient.mk _ (zmod2Action.rangeRestrict 1)) ≠ 0 := by
    intro h0
    have h1g : (1 : End zmod2M).IsGhost := (End.isGhost_iff_cohomologyAction_eq_zero ℤ).mpr
      (by simpa [AlgHom.imageGhostIdealQuotientEquivCohomologyImage_mk_val] using
        congrArg Subtype.val h0)
    have hidH : (homologyFunctor (ModuleCat.{0} ℤ) 0).map
        (𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))) = 0 := by
      have := congrArg (fun f ↦ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.inl ≫ f ≫
        (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.fst) (End.isGhost_iff.mp h1g 0)
      simpa [Category.id_comp, ← Functor.map_comp] using this
    exact hid0 ((homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ 0).mp hidH)
  exact ⟨zmod2M, zmod2Action, zmod2Ghost, hge, hle, hxne, zmod2_ghost_sq, hcohx,
    mem_ghostIdeal_iff.mpr hghostx, zmod2_ghost_ker, hghostker, by simpa using hghostx,
    fun h ↦ hxne (by simpa using congrArg Subtype.val h),
    zmod2Action.imageGhostIdeal_pow_eq_bot 0 1 2 (by omega),
    Subtype.ext (by simpa using hcohx), h1ne⟩

example :
    biprod.inr ≫ zmod2Ghost.asHom ≫ biprod.fst = zmod2Ext1Map ∧
    biprod.inl ≫ zmod2Ghost.asHom ≫ biprod.snd = 0 :=
  ⟨by simp [Category.assoc], by simp [Category.assoc]⟩

end TauCeti.Examples.CohomologyAction
