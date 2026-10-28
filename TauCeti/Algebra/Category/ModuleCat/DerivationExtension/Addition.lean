/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic
public import TauCeti.Algebra.Homology.Ext.BaerSum

/-!
# Addition of derivations and Baer sums of discrete-module extensions

The Baer sum of the self-extensions attached to continuous derivations `δ` and `η`
is the self-extension attached to `δ + η`. This identification takes place in the
abelian category of discrete modules and fixes both endpoints. On the pullback
of the two middle terms it sends `((u, v), (w, v))` to `(u + w, v)`; it descends
through the pushout along addition on the submodule.

The construction uses `DerivationExtension.discreteShortComplex` and
`ShortComplex.baerSum`, whose pullback/pushout construction represents addition
of native extension classes by `ShortComplex.ShortExact.extClass_baerSum`.
The main result is `DerivationExtension.discreteBaerSumIso`.
`DerivationExtension.extClass_discreteShortComplex_add` gives the resulting
additivity of native extension classes under an explicit `HasExt` instance.

The interpretation as infinitesimal deformations follows Edward Frenkel,
*Langlands Correspondence for Loop Groups*, Cambridge University Press (2007).
-/

public section

noncomputable section

namespace TauCeti.DerivationExtension

open CategoryTheory Limits

universe u v w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousAdd A] {δ η : derivationLieAlgebra R A}
  (hδ : Continuous (δ : Module.End R A)) (hη : Continuous (η : Module.End R A))
  (M : (discreteModules.{v} A).FullSubcategory)

private abbrev sumComplex := discreteShortComplex (δ := δ + η) (hδ.add hη) M
private abbrev pairComplex :=
  shortComplexBiprod (discreteShortComplex hδ M) (discreteShortComplex hη M)
private abbrev diagonalPull :=
  (pairComplex hδ hη M).pull (biprod.lift (𝟙 M) (𝟙 M))

private abbrev leftProjection :
    (diagonalPull hδ hη M).X₂ ⟶ (discreteShortComplex hδ M).X₂ :=
  pullback.snd _ _ ≫ biprod.fst

private abbrev rightProjection :
    (diagonalPull hδ hη M).X₂ ⟶ (discreteShortComplex hη M).X₂ :=
  pullback.snd _ _ ≫ biprod.snd

omit [ContinuousAdd A] in
private lemma leftProjection_snd :
    leftProjection hδ hη M ≫ (discreteShortComplex hδ M).g =
      (diagonalPull hδ hη M).g := by
  have h := congrArg (fun f => f ≫ biprod.fst)
    (pullback.condition (f := biprod.lift (𝟙 M) (𝟙 M))
      (g := (pairComplex hδ hη M).g))
  -- Normalize the endpoint carriers before rewriting the pullback equation.
  dsimp only [leftProjection, diagonalPull, pairComplex, shortComplexBiprod,
    discreteShortComplex, shortComplex, ShortComplex.pull] at h ⊢
  simp only [Category.assoc] at h
  erw [biprod.map_fst, biprod.lift_fst, Category.comp_id] at h
  exact h.symm

omit [ContinuousAdd A] in
private lemma rightProjection_snd :
    rightProjection hδ hη M ≫ (discreteShortComplex hη M).g =
      (diagonalPull hδ hη M).g := by
  have h := congrArg (fun f => f ≫ biprod.snd)
    (pullback.condition (f := biprod.lift (𝟙 M) (𝟙 M))
      (g := (pairComplex hδ hη M).g))
  -- Normalize the endpoint carriers before rewriting the pullback equation.
  dsimp only [rightProjection, diagonalPull, pairComplex, shortComplexBiprod,
    discreteShortComplex, shortComplex, ShortComplex.pull] at h ⊢
  simp only [Category.assoc] at h
  erw [biprod.map_snd, biprod.lift_snd, Category.comp_id] at h
  exact h.symm

-- This is the coordinate calculation before passing to bundled category objects.
private def addLift {P N : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup N] [Module A N]
    (f : P →ₗ[A] DerivationExtension δ N) (g : P →ₗ[A] DerivationExtension η N)
    (p : P →ₗ[A] N) (hf : sndHom δ N ∘ₗ f = p) (hg : sndHom η N ∘ₗ g = p) :
    P →ₗ[A] DerivationExtension (δ + η) N where
  toFun x := ⟨(f x).fst + (g x).fst, p x⟩
  map_add' x y := by
    ext
    · simp only [map_add, fst_add]
      abel
    · simp
  map_smul' a x := by
    have hf' : (f x).snd = p x := by
      simpa only [LinearMap.comp_apply, sndHom_apply] using
        congrArg (fun q : P →ₗ[A] N => q x) hf
    have hg' : (g x).snd = p x := by
      simpa only [LinearMap.comp_apply, sndHom_apply] using
        congrArg (fun q : P →ₗ[A] N => q x) hg
    ext
    · simp only [map_smul, fst_smul, RingHom.id_apply, hf', hg', smul_add]
      have hadd : ((δ + η : derivationLieAlgebra R A) : Module.End R A) a =
          (δ : Module.End R A) a + (η : Module.End R A) a := rfl
      rw [hadd, add_smul]
      abel
    · simp

private def pullSum : (diagonalPull hδ hη M).X₂ ⟶ (sumComplex hδ hη M).X₂ :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (addLift (leftProjection hδ hη M).hom.hom (rightProjection hδ hη M).hom.hom
      (diagonalPull hδ hη M).g.hom.hom
      (congrArg (fun f => f.hom.hom) (leftProjection_snd hδ hη M))
      (congrArg (fun f => f.hom.hom) (rightProjection_snd hδ hη M))))

private lemma diagonalPull_f_pullSum :
    (diagonalPull hδ hη M).f ≫ pullSum hδ hη M =
      biprod.desc (𝟙 M) (𝟙 M) ≫ (sumComplex hδ hη M).f := by
  have hl : (diagonalPull hδ hη M).f ≫ leftProjection hδ hη M =
      biprod.fst ≫ (discreteShortComplex hδ M).f := by
    dsimp only [leftProjection, diagonalPull, pairComplex, shortComplexBiprod,
      discreteShortComplex, shortComplex, ShortComplex.pull]
    erw [pullback.lift_snd_assoc, biprod.map_fst]
  have hr : (diagonalPull hδ hη M).f ≫ rightProjection hδ hη M =
      biprod.snd ≫ (discreteShortComplex hη M).f := by
    dsimp only [rightProjection, diagonalPull, pairComplex, shortComplexBiprod,
      discreteShortComplex, shortComplex, ShortComplex.pull]
    erw [pullback.lift_snd_assoc, biprod.map_snd]
  apply (discreteModules A).ι.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hlx : (leftProjection hδ hη M).hom.hom ((diagonalPull hδ hη M).f.hom.hom x) =
      inlHom δ M.obj ((biprod.fst : M ⊞ M ⟶ M).hom.hom x) :=
    congrArg (fun f => f.hom.hom x) hl
  have hrx : (rightProjection hδ hη M).hom.hom ((diagonalPull hδ hη M).f.hom.hom x) =
      inlHom η M.obj ((biprod.snd : M ⊞ M ⟶ M).hom.hom x) :=
    congrArg (fun f => f.hom.hom x) hr
  have hzero : (diagonalPull hδ hη M).g.hom.hom
      ((diagonalPull hδ hη M).f.hom.hom x) = 0 :=
    congrArg (fun f => f.hom.hom x) (diagonalPull hδ hη M).zero
  -- Convert the two concrete-category coercions to the coordinate calculation.
  change (⟨((leftProjection hδ hη M).hom.hom
      ((diagonalPull hδ hη M).f.hom.hom x)).fst +
      ((rightProjection hδ hη M).hom.hom ((diagonalPull hδ hη M).f.hom.hom x)).fst,
      (diagonalPull hδ hη M).g.hom.hom ((diagonalPull hδ hη M).f.hom.hom x)⟩ :
      DerivationExtension (δ + η) M.obj) =
    inlHom (δ + η) M.obj ((biprod.desc (𝟙 M) (𝟙 M)).hom.hom x)
  apply DerivationExtension.ext
  · dsimp only
    rw [hlx, hrx]
    simp only [fst_inlHom]
    have hc : (biprod.desc (𝟙 M) (𝟙 M) : M ⊞ M ⟶ M) = biprod.fst + biprod.snd := by
      simp [biprod.desc_eq]
    rw [hc]
    rfl
  · simpa only [snd_inlHom] using hzero

private lemma pullSum_g :
    pullSum hδ hη M ≫ (sumComplex hδ hη M).g =
      (diagonalPull hδ hη M).g := by
  apply (discreteModules A).ι.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  -- Identify the bundled projection with its named linear-map API.
  change sndHom (δ + η) M.obj ((pullSum hδ hη M).hom.hom x) =
    (diagonalPull hδ hη M).g.hom.hom x
  erw [sndHom_apply]
  rfl

private def baerSumHom :
    (discreteShortComplex hδ M).baerSum
      (discreteShortComplex hη M).f (discreteShortComplex hη M).g
      (discreteShortComplex hη M).zero ⟶ sumComplex hδ hη M where
  τ₁ := 𝟙 M
  τ₂ := pushout.desc (pullSum hδ hη M) (sumComplex hδ hη M).f
    (diagonalPull_f_pullSum hδ hη M)
  τ₃ := 𝟙 M
  comm₁₂ := by
    dsimp only [ShortComplex.baerSum, ShortComplex.push, discreteShortComplex, sumComplex,
      diagonalPull, pairComplex, shortComplexBiprod, shortComplex, ShortComplex.pull]
    erw [pushout.inr_desc]
    simp
  comm₂₃ := by
    dsimp only [ShortComplex.baerSum, ShortComplex.push, discreteShortComplex, sumComplex,
      diagonalPull, pairComplex, shortComplexBiprod, shortComplex, ShortComplex.pull]
    apply pushout.hom_ext
    · erw [pushout.inl_desc_assoc, pushout.inl_desc]
      exact pullSum_g hδ hη M
    · erw [pushout.inr_desc_assoc, pushout.inr_desc]
      exact (sumComplex hδ hη M).zero

/-- The Baer sum of the discrete-module self-extensions for `δ` and `η` is
isomorphic to the self-extension for `δ + η`, by an isomorphism inducing the
identity on both the submodule and the quotient. -/
def discreteBaerSumIso :
    (discreteShortComplex hδ M).baerSum
      (discreteShortComplex hη M).f (discreteShortComplex hη M).g
      (discreteShortComplex hη M).zero ≅ discreteShortComplex (δ := δ + η) (hδ.add hη) M := by
  let φ := baerSumHom hδ hη M
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 M))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (𝟙 M))
  have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    ((shortExact_discreteShortComplex hδ M).baerSum
      (shortExact_discreteShortComplex hη M))
    (shortExact_discreteShortComplex (δ := δ + η) (hδ.add hη) M)
  have : IsIso φ := ShortComplex.isIso_of_isIso φ
  exact asIso φ

/-- The Baer-sum comparison fixes the submodule. -/
@[simp]
lemma discreteBaerSumIso_hom_τ₁ : (discreteBaerSumIso hδ hη M).hom.τ₁ = 𝟙 M := (rfl)

/-- The Baer-sum comparison fixes the quotient. -/
@[simp]
lemma discreteBaerSumIso_hom_τ₃ : (discreteBaerSumIso hδ hη M).hom.τ₃ = 𝟙 M := (rfl)

/-- On the pullback of the two middle terms, the Baer-sum comparison adds
submodule coordinates and retains the common quotient coordinate. -/
@[simp]
lemma discreteBaerSumIso_hom_τ₂_inl :
    let B := shortComplexBiprod (discreteShortComplex hδ M) (discreteShortComplex hη M)
    let P := B.pull (biprod.lift (𝟙 M) (𝟙 M))
    ∀ x : P.X₂.obj,
      (discreteBaerSumIso hδ hη M).hom.τ₂.hom.hom
          ((pushout.inl P.f (biprod.desc (𝟙 M) (𝟙 M))).hom.hom x) =
        ⟨((pullback.snd (biprod.lift (𝟙 M) (𝟙 M)) B.g ≫ biprod.fst).hom.hom x).fst +
          ((pullback.snd (biprod.lift (𝟙 M) (𝟙 M)) B.g ≫ biprod.snd).hom.hom x).fst,
          P.g.hom.hom x⟩ := by
  intro B P x
  have h : pushout.inl (diagonalPull hδ hη M).f (biprod.desc (𝟙 M) (𝟙 M)) ≫
      (discreteBaerSumIso hδ hη M).hom.τ₂ = pullSum hδ hη M := by
    dsimp only [discreteBaerSumIso, asIso, baerSumHom]
    exact pushout.inl_desc _ _ _
  exact congrArg (fun f => f.hom.hom x) h

/-- The inverse Baer-sum comparison fixes the submodule. -/
@[simp]
lemma discreteBaerSumIso_inv_τ₁ : (discreteBaerSumIso hδ hη M).inv.τ₁ = 𝟙 M := by
  have h : (𝟙 M : M ⟶ M) ≫ (discreteBaerSumIso hδ hη M).inv.τ₁ = 𝟙 M :=
    congrArg ShortComplex.Hom.τ₁ (discreteBaerSumIso hδ hη M).hom_inv_id
  exact (Category.id_comp _).symm.trans h

/-- The inverse Baer-sum comparison fixes the quotient. -/
@[simp]
lemma discreteBaerSumIso_inv_τ₃ : (discreteBaerSumIso hδ hη M).inv.τ₃ = 𝟙 M := by
  have h : (𝟙 M : M ⟶ M) ≫ (discreteBaerSumIso hδ hη M).inv.τ₃ = 𝟙 M :=
    congrArg ShortComplex.Hom.τ₃ (discreteBaerSumIso hδ hη M).hom_inv_id
  exact (Category.id_comp _).symm.trans h

/-- Addition of continuous derivations becomes addition of their native
self-extension classes in the category of discrete modules, whenever this
category has native `Ext`. The explicit endpoint type on `Add.add` avoids
unfolding the short-complex carriers during instance synthesis. -/
lemma extClass_discreteShortComplex_add [HasExt.{w} (discreteModules.{v} A).FullSubcategory] :
    ((shortExact_discreteShortComplex (δ := δ + η) (hδ.add hη) M).extClass :
        Abelian.Ext.{w} M M 1) =
      Add.add (α := Abelian.Ext.{w} M M 1)
        (shortExact_discreteShortComplex hδ M).extClass
        (shortExact_discreteShortComplex hη M).extClass := by
  have h := ((shortExact_discreteShortComplex hδ M).baerSum
    (shortExact_discreteShortComplex hη M)).extClass_naturality
      (shortExact_discreteShortComplex (δ := δ + η) (hδ.add hη) M)
      (discreteBaerSumIso hδ hη M).hom
  rw [discreteBaerSumIso_hom_τ₁, discreteBaerSumIso_hom_τ₃] at h
  -- The endpoint identifications are definitional; `erw` makes them available
  -- to the native Ext identity and Baer-sum equations.
  erw [Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_id_comp] at h
  exact h.symm.trans ((shortExact_discreteShortComplex hδ M).extClass_baerSum
    (shortExact_discreteShortComplex hη M))

end TauCeti.DerivationExtension
