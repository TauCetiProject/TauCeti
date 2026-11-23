/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.AffineModel
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Products
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure
public import TauCeti.AlgebraicGeometry.Scheme.DenseAffineCover
public import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Chow's lemma over an affine base

A separated scheme of finite type over an affine base, with finitely many irreducible
components, admits a surjective modification with quasi-projective source. The modification
itself has a closed embedding into a finite-dimensional projective space over its target.
If the original scheme is proper over the base, the modified scheme is projective over it.

The construction embeds the members of a dense finite affine cover into projective closures,
uses the Segre embedding for their product, and takes the closure of the graph of the common
open. No reducedness, integrality or field hypothesis is imposed.

## References

* The Stacks Project, Section 30.18, *Chow's Lemma* (tag 0200).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

private theorem exists_chowTarget {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [LocallyOfFiniteType f]
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : ∀ a, IsAffineOpen (V a))
    (hcover : iSup V = ⊤) (U : X.Opens) [QuasiCompact U.ι] (hUV : ∀ a, U ≤ V a) :
    ∃ (T : Over (Spec (.of R))) (_ : IsProper T.hom) (τ : Type u) (_ : Finite τ)
      (E : T ⟶ Over.mk (Proj.toSpecCoeff (homogeneousSubmodule τ R)))
      (_ : IsClosedImmersion E.left) (g : Over.mk (U.ι ≫ f) ⟶ T),
      IsImmersion (graphClosureSnd f T.hom U g.left (Over.w g)) := by
  classical
  have hmodels (a : ι) :=
    have : IsAffine (V a).toScheme := hV a
    TauCeti.exists_projectiveClosedModel ((V a).ι ≫ f)
  choose σ hσ P j e hj he using hmodels
  have : ∀ a, Finite (σ a) := hσ
  have : ∀ a, IsOpenImmersion (j a).left := hj
  have : ∀ a, IsClosedImmersion (e a).left := he
  have : ∀ a, IsSeparated (P a).hom := fun a ↦ by
    rw [← Over.w (e a)]
    -- Over.w gives an equality of structure morphisms; expose its underlying composite.
    change IsSeparated ((e a).left ≫ Proj.toSpecCoeff (homogeneousSubmodule (σ a) R))
    infer_instance
  let T : Over (Spec (.of R)) := ∏ᶜ P
  obtain ⟨τ, hτ, E, hE⟩ := Proj.exists_isClosedImmersion_finite_product R P
    (fun a ↦ ⟨σ a, hσ a, e a, he a⟩)
  have : IsClosedImmersion E.left := hE
  have : Finite τ := hτ
  have : IsProper (Proj.toSpecCoeff (homogeneousSubmodule τ R)) :=
    inferInstanceAs (IsProper (Proj (homogeneousSubmodule τ R) ↘ Spec (.of R)))
  have : IsProper T.hom := by
    rw [← Over.w E]
    -- Properness is tested on the underlying scheme composite after rewriting Over.w.
    change IsProper (E.left ≫ Proj.toSpecCoeff (homogeneousSubmodule τ R))
    infer_instance
  let v : ∀ a, Over.mk (U.ι ≫ f) ⟶ P a := fun a ↦
    Over.homMk (X.homOfLE (hUV a) ≫ (j a).left) (by
      rw [Category.assoc, Over.w]
      -- Expose the source structure map of Over.mk to apply the open-inclusion equation.
      change X.homOfLE (hUV a) ≫ (V a).ι ≫ f = U.ι ≫ f
      rw [← Category.assoc, Scheme.homOfLE_ι])
  let g : Over.mk (U.ι ≫ f) ⟶ T := Pi.lift v
  refine ⟨T, inferInstance, τ, hτ, E, hE, g, ?_⟩
  exact isImmersion_graphClosureSnd hcover hUV
    (fun a ↦ Over.w (Pi.π P a)) (fun a ↦ Over.w (j a)) (fun a ↦ by
      exact congrArg (fun b : Over.mk (U.ι ≫ f) ⟶ P a ↦ b.left) (Pi.lift_comp_π v a))

private theorem exists_chowModification_of_target
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (U : X.Opens) [QuasiCompact U.ι] (hU : Dense (U : Set X))
    (T : Over (Spec (.of R))) [IsProper T.hom] {τ : Type u}
    (E : T ⟶ Over.mk (Proj.toSpecCoeff (homogeneousSubmodule τ R)))
    [IsClosedImmersion E.left] (g : Over.mk (U.ι ≫ f) ⟶ T)
    [IsImmersion (graphClosureSnd f T.hom U g.left (Over.w g))] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X)
      (i : Y ⟶ Proj (homogeneousSubmodule τ R))
      (h : p ≫ f = i ≫ Proj.toSpecCoeff (homogeneousSubmodule τ R)),
      IsModification p ∧ Surjective p ∧ IsImmersion i ∧
        IsClosedImmersion (pullback.lift p i h) := by
  let hg := Over.w g
  let Y := graphClosure f T.hom U g.left hg
  let p : Y ⟶ X := graphClosureFst f T.hom U g.left hg
  let q : Y ⟶ T.left := graphClosureSnd f T.hom U g.left hg
  have hp : IsModification p := isModification_graphClosureFst hU
  let i := q ≫ E.left
  have hi : IsImmersion i := inferInstance
  have h : p ≫ f = i ≫ Proj.toSpecCoeff (homogeneousSubmodule τ R) := by
    -- Expand the selected projective immersion before applying the embedding base equation.
    rw [show i = q ≫ E.left from rfl, Category.assoc]
    have hE : E.left ≫ Proj.toSpecCoeff (homogeneousSubmodule τ R) = T.hom := E.w
    rw [hE]
    exact graphClosureFst_comp f T.hom U g.left hg
  have hsurj : Surjective p := inferInstance
  have hgraphImm : IsImmersion (pullback.lift p i h) := by
    have : IsImmersion (pullback.lift p i h ≫
        pullback.snd f (Proj.toSpecCoeff (homogeneousSubmodule τ R))) := by
      simpa only [pullback.lift_snd] using hi
    exact IsImmersion.of_comp _ (pullback.snd f (Proj.toSpecCoeff (homogeneousSubmodule τ R)))
  have hgraphProper : IsProper (pullback.lift p i h) := by
    have : IsProper (pullback.lift p i h ≫
        pullback.fst f (Proj.toSpecCoeff (homogeneousSubmodule τ R))) := by
      simpa only [pullback.lift_fst] using (inferInstance : IsProper p)
    exact IsProper.of_comp _ (pullback.fst f (Proj.toSpecCoeff (homogeneousSubmodule τ R)))
  exact ⟨Y, p, i, h, hp, hsurj, hi,
    IsClosedImmersion.of_isPreimmersion _
      (pullback.lift p i h).isClosedMap.isClosed_range⟩

/-- **Chow's lemma over an affine base.** A separated scheme of finite type with finitely
many irreducible components admits a surjective modification whose source immerses into a
finite-dimensional projective space over the base. The same immersion gives a closed embedding
over the original scheme, so the modification morphism is projective. -/
theorem exists_chowModification_of_finite_irreducibleComponents
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : (irreducibleComponents X).Finite) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (σ : Type u) (_ : Finite σ)
      (i : Y ⟶ Proj (homogeneousSubmodule σ R))
      (h : p ≫ f = i ≫ Proj.toSpecCoeff (homogeneousSubmodule σ R)),
      IsModification p ∧ Surjective p ∧ IsImmersion i ∧
        IsClosedImmersion (pullback.lift p i h) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨s, hs, hd⟩ := X.exists_finite_affine_cover_dense_iInter hX
  let V : s → X.Opens := fun A ↦ A.val.val
  have hV : iSup V = ⊤ := by simpa only [V, iSup_subtype] using hs
  let U : X.Opens := ⨅ A, V A
  have hU : Dense (U : Set X) := by
    simpa only [U, V, Opens.coe_iInf, Set.iInter_subtype] using hd
  have hcompactU : IsCompact (U : Set X) := by
    have hc := QuasiSeparatedSpace.isCompact_sInter (α := X)
      (s := Set.range fun A ↦ (V A : Set X)) (Set.finite_range _)
      (by rintro _ ⟨A, rfl⟩; exact Or.inl (V A).isOpen)
      (by rintro _ ⟨A, rfl⟩; exact A.val.property.isCompact)
    simpa only [U, Set.sInter_range, Opens.coe_iInf] using hc
  have : CompactSpace U := isCompact_iff_compactSpace.mp hcompactU
  have : QuasiCompact U.ι := (quasiCompact_iff_compactSpace _).mpr inferInstance
  obtain ⟨T, hT, τ, hτ, E, hE, g, hg⟩ :=
    exists_chowTarget f V (fun A ↦ A.val.property) hV U (iInf_le V)
  have : IsProper T.hom := hT
  have : Finite τ := hτ
  have : IsClosedImmersion E.left := hE
  have : IsImmersion (graphClosureSnd f T.hom U g.left (Over.w g)) := hg
  obtain ⟨Y, p, i, h, hp, hs, hi, hc⟩ := exists_chowModification_of_target f U hU T E g
  exact ⟨Y, p, τ, hτ, i, h, hp, hs, hi, hc⟩

/-- A proper scheme over an affine base with finitely many irreducible components has a
surjective modification by a scheme projective over that base. -/
theorem exists_projectiveModification_of_finite_irreducibleComponents
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hX : (irreducibleComponents X).Finite) :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of R))) (p : Y ⟶ X),
      IsModification p ∧ Surjective p ∧ Y.IsProjectiveOver R ∧
        (Y ↘ Spec (.of R)) = p ≫ f := by
  obtain ⟨Y, p, σ, hσ, i, h, hp, hs, hi, -⟩ :=
    exists_chowModification_of_finite_irreducibleComponents f hX
  have : Finite σ := hσ
  have : IsProper (i ≫ Proj.toSpecCoeff (homogeneousSubmodule σ R)) := by
    rw [← h]
    infer_instance
  have : IsProper i := IsProper.of_comp _ (Proj.toSpecCoeff (homogeneousSubmodule σ R))
  have : IsClosedImmersion i := .of_isPreimmersion _ i.isClosedMap.isClosed_range
  let : Y.Over (Spec (.of R)) := ⟨p ≫ f⟩
  have : i.IsOver (Spec (.of R)) := ⟨h.symm⟩
  exact ⟨Y, inferInstance, p, hp, hs,
    Scheme.IsProjectiveOver.of_isClosedImmersion R i, rfl⟩

/-- A proper scheme over a Noetherian affine base admits a surjective modification by a
projective scheme. -/
theorem exists_projectiveModification {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of R))) (p : Y ⟶ X),
      IsModification p ∧ Surjective p ∧ Y.IsProjectiveOver R ∧
        (Y ↘ Spec (.of R)) = p ≫ f := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  exact exists_projectiveModification_of_finite_irreducibleComponents f
    NoetherianSpace.finite_irreducibleComponents

end TauCeti.AlgebraicGeometry
