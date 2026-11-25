/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# The triangle of mapping cones of two monomorphisms, up to quasi-isomorphism

For composable morphisms `a : X ⟶ Y` and `b : Y ⟶ Z` of cochain complexes in an abelian category,
Mathlib's triangle of mapping cones `cone a ⟶ cone (a ≫ b) ⟶ cone b ⟶ (cone a)⟦1⟧`
(`mappingConeCompTriangle a b`) is compared with the sequence of cokernels
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` through the canonical maps
`mappingCone.descShortComplex` from the mapping cones to the cokernels. When `b` is a
monomorphism, the latter sequence is short exact, and the map in cohomology induced by the third
morphism of the triangle is the connecting map of that short exact sequence
(`CochainComplex.mappingCone.shiftMap_mappingConeCompTriangle_mor₃`). This extends Mathlib's
`mappingCone.homologySequenceδ_triangleh`, which is the case `a = 0`.

The file also records a form of Mathlib's `mappingCone.quasiIso_descShortComplex` for maps out of
the mapping cone that are only known to factor through the cokernel: for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, a map `mappingCone (X₁ ⟶ X₂) ⟶ W` vanishing on `X₁` and given on `X₂` by
`X₂ ⟶ X₃ ⟶ W` for a quasi-isomorphism `X₃ ⟶ W` is a quasi-isomorphism
(`CochainComplex.mappingCone.quasiIso_desc_of_shortExact`). This is how a three-term sequence
which is short exact only up to a quasi-isomorphism, such as a Mayer–Vietoris sequence of singular
chains, is shown to have acyclic total complex. In particular, extension by zero along an
embedding into `ComplexShape.up ℤ` carries a sequence `P₄ ⟶ P₂ ⊞ P₃ ⟶ P₁` of homological
complexes, with monomorphic first map `(f₂, -f₃)` and second map `g₂ + g₃` inducing a
quasi-isomorphism from its cokernel, to one whose Mayer–Vietoris map out of the mapping cone of
`(f₂, f₃)` is a quasi-isomorphism
(`CochainComplex.mappingCone.quasiIso_desc_extendMap_of_quasiIso_cokernelDesc`).
-/

public section

open CategoryTheory Limits HomotopyCategory

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : CochainComplex C ℤ} (a : X ⟶ Y)
  (b : Y ⟶ Z) [Mono b]

/-- The map in cohomology induced by the third morphism `cone b ⟶ (cone a)⟦1⟧` of the triangle of
mapping cones of `a` and `b`, read through the canonical maps `cone a ⟶ cokernel a` and
`cone b ⟶ cokernel b` (the latter a quasi-isomorphism, as `b` is a monomorphism), is the
connecting map of the short exact sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`. -/
lemma shiftMap_mappingConeCompTriangle_mor₃ (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (mappingConeCompTriangle a b).mor₃ n₀ n₁ h ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
    HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
      (TauCeti.cokernelCompSequence_shortExact a b).δ n₀ n₁
        (by simp [← h, add_comm]) := by
  -- The connecting map of the triangle of `b` alone, through `homologySequenceδ_triangleh`.
  have hb := homologySequenceδ_triangleh (TauCeti.cokernelSequence_shortExact b) n₀ n₁ (by lia)
  rw [homologySequenceδ_quotient_mapTriangle_obj] at hb
  have hb' : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (triangle b).mor₃ n₀ n₁ h =
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
        (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm]) := by
    have h₁ := (Iso.cancel_iso_hom_left
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₀).app (mappingCone b)) _ _).1 hb
    exact (Iso.cancel_iso_inv_right _ _
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₁).app Y)).1
        (h₁.trans (Category.assoc _ _ _).symm)
  -- The naturality of connecting maps along `(Y ⟶ Z ⟶ cokernel b) ⟶ (cokernel a ⟶ … )`.
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (TauCeti.cokernelSequenceToCokernelCompSequence a b) (TauCeti.cokernelSequence_shortExact b)
    (TauCeti.cokernelCompSequence_shortExact a b) n₀ n₁
    (by simp [← h, add_comm])
  simp only [TauCeti.cokernelSequenceToCokernelCompSequence_τ₃,
    TauCeti.cokernelSequenceToCokernelCompSequence_τ₁] at hnat
  have hnat' := hnat.trans ((congrArg (· ≫ _) (HomologicalComplex.homologyMap_id _ n₀)).trans
    (Category.id_comp _))
  -- `Functor.shiftMap_comp`, applied to the third morphism `(triangle b).mor₃ ≫ (inr a)⟦1⟧'`;
  -- `(homologyFunctor 0).shift n₁` is `homologyFunctor n₁` by `homologyFunctor_shift`.
  have hcomp : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (mappingConeCompTriangle a b).mor₃ n₀ n₁ h =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle b).mor₃ n₀ n₁ h ≫ HomologicalComplex.homologyMap (inr a) n₁ :=
    Functor.shiftMap_comp _ _ _ _ _ _
  have e₁ : HomologicalComplex.homologyMap (inr a) n₁ ≫
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
      HomologicalComplex.homologyMap (cokernel.π a) n₁ :=
    (HomologicalComplex.homologyMap_comp _ _ n₁).symm.trans
      (congrArg (HomologicalComplex.homologyMap · n₁)
        (inr_descShortComplex (ShortComplex.cokernelSequence a)))
  rw [hcomp, hb']
  let A := HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀
  let D := (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm])
  exact (Category.assoc (A ≫ D) _ _).trans <|
    (congrArg (fun t => (A ≫ D) ≫ t) e₁).trans <|
    (Category.assoc A D _).trans (congrArg (fun t => A ≫ t) hnat')

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone

open HomComplex

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (CochainComplex C ℤ)}

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes and a
quasi-isomorphism `h : X₃ ⟶ W`, the map `mappingCone (X₁ ⟶ X₂) ⟶ W` which vanishes on `X₁` and is
`X₂ ⟶ X₃ ⟶ W` on `X₂` is a quasi-isomorphism: it is `descShortComplex S ≫ h`. -/
lemma quasiIso_desc_of_shortExact (hS : S.ShortExact) {W : CochainComplex C ℤ} (h : S.X₃ ⟶ W)
    [QuasiIso h] {ψ : S.X₂ ⟶ W} (hψ : S.g ≫ h = ψ)
    (eq : δ (-1) 0 (0 : Cochain S.X₁ W (-1)) = Cochain.ofHom (S.f ≫ ψ)) :
    QuasiIso (desc S.f 0 ψ eq) := by
  have := quasiIso_descShortComplex hS
  have hd : desc S.f 0 ψ eq = descShortComplex S ≫ h := by
    subst hψ
    ext n
    apply ext_from _ (n + 1) n rfl <;> simp [descShortComplex]
  rw [hd]
  infer_instance

/-- Extension by zero along `e` carries a three-term sequence `P₄ ⟶ P₂ ⊞ P₃ ⟶ P₁` of homological
complexes, with monomorphic first map `(f₂, -f₃)` and second map `g₂ + g₃` inducing a
quasi-isomorphism from its cokernel, to one whose Mayer–Vietoris map
`mappingCone (E f₂, E f₃) ⟶ E P₁`, given by `(E g₂, -E g₃)` as in
`TopCat.KPresheaf.mayerVietorisDesc`, is a quasi-isomorphism. -/
lemma quasiIso_desc_extendMap_of_quasiIso_cokernelDesc {ι : Type*} {c : ComplexShape ι}
    {P₁ P₂ P₃ P₄ : HomologicalComplex C c} (e : c.Embedding (ComplexShape.up ℤ))
    {f₂ : P₄ ⟶ P₂} {f₃ : P₄ ⟶ P₃} {g₂ : P₂ ⟶ P₁} {g₃ : P₃ ⟶ P₁} {a : P₄ ⟶ P₂ ⊞ P₃}
    {b : P₂ ⊞ P₃ ⟶ P₁} [Mono a]
    (hab : a ≫ b = 0) [QuasiIso (cokernel.desc a b hab)] (ha : a = biprod.lift f₂ (-f₃))
    (hb : b = biprod.desc g₂ g₃)
    (eq : δ (-1) 0 (0 : Cochain _ _ (-1)) = Cochain.ofHom
      (biprod.lift (HomologicalComplex.extendMap f₂ e) (HomologicalComplex.extendMap f₃ e) ≫
        biprod.desc (HomologicalComplex.extendMap g₂ e) (-HomologicalComplex.extendMap g₃ e))) :
    QuasiIso (desc (biprod.lift (HomologicalComplex.extendMap f₂ e)
      (HomologicalComplex.extendMap f₃ e)) 0
      (biprod.desc (HomologicalComplex.extendMap g₂ e) (-HomologicalComplex.extendMap g₃ e))
        eq) := by
  subst hb
  let E := e.extendFunctor C
  -- the twisted comparison `θ` carries `E a` and `E (g₂ + g₃)` to the maps of the conclusion
  let θ := E.mapBiprodNegIso P₂ P₃
  have hφ : E.map a ≫ θ.hom = biprod.lift (E.map f₂) (E.map f₃) := by
    subst ha
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [θ, ← E.map_comp]
  have hψ : (θ.inv ≫ E.map (cokernel.π a)) ≫ E.map (cokernel.desc _ _ hab) =
      biprod.desc (E.map g₂) (-E.map g₃) := by
    rw [Category.assoc, ← E.map_comp, cokernel.π_desc, Iso.inv_comp_eq]
    simp [θ, biprod.desc_eq]
  -- so the sequence of the conclusion is short exact up to `E (cokernel a) ⟶ E P₁`
  let S := ShortComplex.mk (biprod.lift (E.map f₂) (E.map f₃)) (θ.inv ≫ E.map (cokernel.π a))
    (by rw [← hφ]; simp [← E.map_comp])
  have hS : S.ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := (ShortComplex.cokernelSequence a).map E) (Iso.refl _) θ
      (Iso.refl _) ((Category.id_comp _).trans hφ.symm)
      ((θ.hom_inv_id_assoc _).trans (Category.comp_id _).symm))
    ((TauCeti.cokernelSequence_shortExact _).extend e)
  have : QuasiIso (E.map (cokernel.desc _ _ hab)) := by
    simp only [E, ComplexShape.Embedding.extendFunctor_map]
    infer_instance
  exact quasiIso_desc_of_shortExact hS _ hψ eq

end CochainComplex.mappingCone
