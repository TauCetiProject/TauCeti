/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.Topology.Algebra.MulAction.Discrete

/-!
# Discrete Galois modules as `GalRep n F` objects

Continuous Galois cohomology on `Field.absoluteGaloisGroup F` uses bundled representations
`A : TauCeti.GalRep n F`, that is, objects of `TopRep (ZMod n) (Field.absoluteGaloisGroup F)` with
Mathlib's `continuousCohomology`. Arithmetic applications—such as Kummer modules, elliptic-curve
torsion, and unramified local duality—instead work with discrete `AbsoluteGaloisGroup F`-modules
`M` equipped with a `Module (ZMod n) M` instance and explicit low-degree cohomology `H⁰`, `H¹`,
`H²`.

This file builds the shared bridge between the two for an arbitrary field `F`:

* `TauCeti.GalRep`: `TopRep (ZMod n) (Field.absoluteGaloisGroup F)`.
* `TauCeti.galRepOfZModModule`: restricts the Galois action on a discrete `ZMod n`-module `M` along
  `TauCeti.absoluteGaloisGroupRestrictEquiv F` to obtain an object of `GalRep n F`, together with
  `galRepOfZModModuleEquiv`, `galRepOfZModModuleEquiv_smul`, `galRepOfZModModuleMap`,
  `galRepOfZModModuleH0Equiv` / `H1Equiv` / `H2Equiv`, and their `coeffMap` naturality theorems
  `galRepOfZModModuleH0Equiv_coeffMap` / `H1Equiv_coeffMap` / `H2Equiv_coeffMap`.
-/

public noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- **Coefficient objects for the absolute Galois group with `ZMod n` scalars**: topological
representations of `G_F = Field.absoluteGaloisGroup F` over `ZMod n`, on which Mathlib's
`continuousCohomology` is defined. -/
abbrev GalRep : Type (u + 1) :=
  TopRep.{u} (ZMod n) (Field.absoluteGaloisGroup F)

section ZModModule

variable (M : Type u) [AddCommGroup M] [Module (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup F) M]

/-- **Bundle a discrete `G_F`-module with a `ZMod n`-module structure as an object of
`GalRep n F`**, restricting the Galois action along `TauCeti.absoluteGaloisGroupRestrictEquiv F`. -/
def galRepOfZModModule : GalRep n F :=
  haveI : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
    (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) M)

/-- The carrier of `galRepOfZModModule n F M` has the discrete topology. -/
instance : DiscreteTopology (galRepOfZModModule n F M).V :=
  inferInstanceAs (DiscreteTopology M)

/-- The coefficient dictionary `M ≃+ (galRepOfZModModule n F M).V`. -/
def galRepOfZModModuleEquiv : M ≃+ (galRepOfZModModule n F M).V :=
  AddEquiv.refl M

/-- Finiteness of `(galRepOfZModModule n F M).V` when `M` is finite. -/
instance [Finite M] : Finite (galRepOfZModModule n F M).V :=
  Finite.of_equiv M (galRepOfZModModuleEquiv n F M).toEquiv

/-- **The coefficient dictionary is equivariant**: `g ∈ Field.absoluteGaloisGroup F` acts on
`galRepOfZModModule n F M` as its restriction to the separable closure acts on `M`. -/
@[simp]
theorem galRepOfZModModuleEquiv_smul (g : Field.absoluteGaloisGroup F) (x : M) :
    galRepOfZModModuleEquiv n F M (absoluteGaloisGroupRestrictEquiv F g • x) =
      (galRepOfZModModule n F M).ρ g (galRepOfZModModuleEquiv n F M x) := by
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (ofDiscreteModule_ρ_apply_apply (R := ZMod n)
      (absoluteGaloisGroupRestrictEquiv F g) x).symm.trans
    (ContRepresentation.restrict_apply_apply
      (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) M).ρ
      (absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F) g x).symm

attribute [local instance] TopRep.distribMulAction

/-- **Degree-zero cohomology comparison** between explicit `H⁰(G_F, M)` and
`continuousCohomology 0 (galRepOfZModModule n F M)`. -/
def galRepOfZModModuleH0Equiv :
    H0 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 0 (galRepOfZModModule n F M) :=
  ((AddEquiv.ofBijective
      (explicitMap0 (AbsoluteGaloisGroup F) M
        (absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (galRepOfZModModuleEquiv n F M).toAddMonoidHom
        fun g x ↦ (galRepOfZModModuleEquiv_smul n F M g x).trans
          (TopRep.distribMulAction_smul _ g _).symm)
      (explicitMap0_bijective (AbsoluteGaloisGroup F) M
        (absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (absoluteGaloisGroupRestrictEquiv F).surjective
        (galRepOfZModModuleEquiv n F M).toAddMonoidHom
        (galRepOfZModModuleEquiv n F M).bijective
        fun g x ↦ (galRepOfZModModuleEquiv_smul n F M g x).trans
          (TopRep.distribMulAction_smul _ g _).symm)).trans
    (explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V).toContinuousLinearEquiv.toAddEquiv).trans
    (ofDiscreteModuleRestrictScalarsIntEquiv (galRepOfZModModule n F M) 0)

/-- `galRepOfZModModuleH0Equiv` is pullback along `absoluteGaloisGroupRestrictEquiv F`
followed by the degree-zero comparison with canonical continuous cohomology. -/
theorem galRepOfZModModuleH0Equiv_apply (x : H0 (AbsoluteGaloisGroup F) M) :
    galRepOfZModModuleH0Equiv n F M x =
      ofDiscreteModuleRestrictScalarsIntEquiv (galRepOfZModModule n F M) 0
        ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F)
            (galRepOfZModModule n F M).V).toContinuousLinearEquiv.toAddEquiv
          (explicitMap0 (AbsoluteGaloisGroup F) M
            (absoluteGaloisGroupRestrictEquiv F :
              Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
            (galRepOfZModModuleEquiv n F M).toAddMonoidHom
            (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
              (TopRep.distribMulAction_smul _ g _).symm) x)) :=
  (rfl)

variable [ContinuousSMul (AbsoluteGaloisGroup F) M]

/-- `galRepOfZModModule n F M` is smooth and discrete when `G_F` acts continuously on `M`. -/
theorem isSmoothDiscrete_galRepOfZModModule :
    IsSmoothDiscrete (ZMod n) (galRepOfZModModule n F M) := by
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (ofDiscreteModule_isSmoothDiscrete (ZMod n) (AbsoluteGaloisGroup F) M).res
    (absoluteGaloisGroupRestrictEquiv F).continuous

/-- `Fact` instance for `isSmoothDiscrete_galRepOfZModModule`. -/
instance : Fact (IsSmoothDiscrete (ZMod n) (galRepOfZModModule n F M)) :=
  ⟨isSmoothDiscrete_galRepOfZModModule n F M⟩

attribute [local instance] TopRep.distribMulAction

/-- The action of `Field.absoluteGaloisGroup F` on `galRepOfZModModule n F M` is continuous. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup F) (galRepOfZModModule n F M).V :=
  (isSmoothDiscrete_galRepOfZModModule n F M).continuousSMul

/-- **Degree-one cohomology comparison** between explicit `H¹(G_F, M)` and
`continuousCohomology 1 (galRepOfZModModule n F M)`. -/
def galRepOfZModModuleH1Equiv :
    H1 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 1 (galRepOfZModModule n F M) :=
  (explicitMap1Equiv (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M) continuous_of_discreteTopology
      continuous_of_discreteTopology
      fun g x ↦ (galRepOfZModModuleEquiv_smul n F M g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans
    (galRepOfZModModule n F M).explicitH1AddEquivContinuousCohomologyOfDiscrete

/-- `galRepOfZModModuleH1Equiv` is degree-one pullback along
`absoluteGaloisGroupRestrictEquiv F` followed by the comparison with canonical continuous
cohomology. -/
theorem galRepOfZModModuleH1Equiv_apply (x : H1 (AbsoluteGaloisGroup F) M) :
    galRepOfZModModuleH1Equiv n F M x =
      (galRepOfZModModule n F M).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (explicitMap1 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
          (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
          (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
          (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [galRepOfZModModuleH1Equiv, AddEquiv.trans_apply, explicitMap1Equiv_apply]

/-- **Degree-two cohomology comparison** between explicit `H²(G_F, M)` and
`continuousCohomology 2 (galRepOfZModModule n F M)`. -/
def galRepOfZModModuleH2Equiv :
    H2 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 2 (galRepOfZModModule n F M) :=
  (explicitMap2Equiv (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M) continuous_of_discreteTopology
      continuous_of_discreteTopology
      fun g x ↦ (galRepOfZModModuleEquiv_smul n F M g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans
    (galRepOfZModModule n F M).explicitH2AddEquivContinuousCohomologyOfDiscrete

/-- `galRepOfZModModuleH2Equiv` is degree-two pullback along
`absoluteGaloisGroupRestrictEquiv F` followed by the comparison with canonical continuous
cohomology. -/
theorem galRepOfZModModuleH2Equiv_apply (x : H2 (AbsoluteGaloisGroup F) M) :
    galRepOfZModModuleH2Equiv n F M x =
      (galRepOfZModModule n F M).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
          (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
          (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
          (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [galRepOfZModModuleH2Equiv, AddEquiv.trans_apply, explicitMap2Equiv_apply]

end ZModModule

section ZModModuleMap

variable {M N : Type u} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction (AbsoluteGaloisGroup F) M]
  [AddCommGroup N] [Module (ZMod n) N] [TopologicalSpace N]
  [DiscreteTopology N] [DistribMulAction (AbsoluteGaloisGroup F) N]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **Bundle an equivariant additive homomorphism of discrete `ZMod n[G_F]`-modules as a morphism
in `GalRep n F`.** -/
def galRepOfZModModuleMap (f : M →+[AbsoluteGaloisGroup F] N) :
    galRepOfZModModule n F M ⟶ galRepOfZModModule n F N :=
  TopRep.ofHom
    { toContinuousLinearMap := ⟨f.toAddMonoidHom.toZModLinearMap n, continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext m
        let m₀ : M := (galRepOfZModModuleEquiv n F M).symm m
        have hm : (galRepOfZModModule n F M).ρ g m =
            galRepOfZModModuleEquiv n F M (absoluteGaloisGroupRestrictEquiv F g • m₀) :=
          (galRepOfZModModuleEquiv_smul n F M g m₀).symm
        have hm' : (galRepOfZModModule n F N).ρ g (f m₀) =
            galRepOfZModModuleEquiv n F N (absoluteGaloisGroupRestrictEquiv F g • f m₀) :=
          (galRepOfZModModuleEquiv_smul n F N g (f m₀)).symm
        change f ((galRepOfZModModule n F M).ρ g m) = (galRepOfZModModule n F N).ρ g (f m₀)
        rw [hm, hm']
        exact map_smul f (absoluteGaloisGroupRestrictEquiv F g) m₀ }

/-- `galRepOfZModModuleMap` intertwines the coefficient dictionaries `galRepOfZModModuleEquiv`. -/
@[simp]
theorem galRepOfZModModuleMap_hom_galRepOfZModModuleEquiv
    (f : M →+[AbsoluteGaloisGroup F] N) (m : M) :
    (galRepOfZModModuleMap n F f).hom (galRepOfZModModuleEquiv n F M m) =
      galRepOfZModModuleEquiv n F N (f m) :=
  (rfl)

/-- The identity coefficient map induces the identity morphism in `GalRep n F`. -/
@[simp]
theorem galRepOfZModModuleMap_id :
    galRepOfZModModuleMap n F (DistribMulActionHom.id (AbsoluteGaloisGroup F) : M →+[_] M) =
      𝟙 (galRepOfZModModule n F M) := by
  ext m
  rfl

/-- Composition of equivariant coefficient maps induces composition of morphisms in `GalRep n F`. -/
theorem galRepOfZModModuleMap_comp {P : Type u} [AddCommGroup P] [Module (ZMod n) P]
    [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction (AbsoluteGaloisGroup F) P]
    (f : M →+[AbsoluteGaloisGroup F] N) (q : N →+[AbsoluteGaloisGroup F] P) :
    galRepOfZModModuleMap n F (q.comp f) =
      galRepOfZModModuleMap n F f ≫ galRepOfZModModuleMap n F q := by
  ext m
  rfl

/-- **Degree-zero naturality of `galRepOfZModModuleH0Equiv`**: the degree-zero comparison carries
`explicitCoeff0` to `TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 0`. -/
theorem galRepOfZModModuleH0Equiv_coeffMap
    (f : M →+[AbsoluteGaloisGroup F] N) (x : H0 (AbsoluteGaloisGroup F) M) :
    TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 0
        (galRepOfZModModuleH0Equiv n F M x) =
      galRepOfZModModuleH0Equiv n F N (explicitCoeff0 (AbsoluteGaloisGroup F) M f x) := by
  let X := galRepOfZModModule n F M
  let Y := galRepOfZModModule n F N
  let Fhom : X ⟶ Y := galRepOfZModModuleMap n F f
  let fV : X.V →+ Y.V :=
    ((galRepOfZModModuleEquiv n F N).toAddMonoidHom.comp f.toAddMonoidHom).comp
      (galRepOfZModModuleEquiv n F M).symm.toAddMonoidHom
  let fGal : X.V →+[Field.absoluteGaloisGroup F] Y.V :=
    { fV with
      map_smul' g m := by
        let m₀ : M := (galRepOfZModModuleEquiv n F M).symm m
        have hm : g • m =
            galRepOfZModModuleEquiv n F M (absoluteGaloisGroupRestrictEquiv F g • m₀) :=
          (TopRep.distribMulAction_smul X g m).trans
            (galRepOfZModModuleEquiv_smul n F M g m₀).symm
        have hm' : g • galRepOfZModModuleEquiv n F N (f m₀) =
            galRepOfZModModuleEquiv n F N (absoluteGaloisGroupRestrictEquiv F g • f m₀) :=
          (TopRep.distribMulAction_smul Y g _).trans
            (galRepOfZModModuleEquiv_smul n F N g (f m₀)).symm
        have h1 : fV (g • m) = galRepOfZModModuleEquiv n F N
            (f (absoluteGaloisGroupRestrictEquiv F g • m₀)) := by
          dsimp only [fV]
          rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hm]
          rfl
        have h2 : fV m = galRepOfZModModuleEquiv n F N (f m₀) := rfl
        change fV (g • m) = g • fV m
        rw [h1, h2, hm']
        exact congrArg (galRepOfZModModuleEquiv n F N)
          (map_smul f (absoluteGaloisGroupRestrictEquiv F g) m₀) }
  let Fint : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) X.V ⟶
      ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) Y.V :=
    ofDiscreteModuleMap fGal.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul fGal g m
  have hcomm : Fint ≫ eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj Y) =
      eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj X) ≫
        TopRep.restrictScalarsInt.map Fhom := by
    have keyComm : ∀ {A B : TopRep ℤ (Field.absoluteGaloisGroup F)}
        (hA : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) X.V = A)
        (hB : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) Y.V = B)
        (g' : A ⟶ B),
        (∀ m : (ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) X.V).V,
          g'.hom (cast (congrArg TopRep.V hA) m) =
            cast (congrArg TopRep.V hB) (Fint.hom m)) →
        Fint ≫ eqToHom hB = eqToHom hA ≫ g' := by
      rintro A B rfl rfl g' hg'
      ext m
      exact (hg' m).symm
    refine keyComm (ofDiscreteModule_eq_restrictScalarsInt_obj X)
      (ofDiscreteModule_eq_restrictScalarsInt_obj Y) (TopRep.restrictScalarsInt.map Fhom)
      fun m ↦ ?_
    rw [cast_ofDiscreteModule_eq_restrictScalarsInt_obj X,
      cast_ofDiscreteModule_eq_restrictScalarsInt_obj Y]
    have hFhom : (TopRep.restrictScalarsInt.map Fhom).hom (show X.V from m) =
        Fhom.hom (show X.V from m) :=
      TopRep.restrictScalarsInt_map_hom_apply Fhom (show X.V from m)
    have hFint : Fint.hom m = fGal m :=
      ofDiscreteModuleMap_hom_apply fGal.toAddMonoidHom.toIntLinearMap
        (fun g x ↦ map_smul fGal g x) m
    rw [hFhom, hFint]
    rfl
  have hcoeffEq :
      TauCeti.ContinuousCohomology.coeffMap Fint 0 ≫
          eqToHom (congrArg (continuousCohomology 0)
            (ofDiscreteModule_eq_restrictScalarsInt_obj Y)) =
        eqToHom (congrArg (continuousCohomology 0)
            (ofDiscreteModule_eq_restrictScalarsInt_obj X)) ≫
          TauCeti.ContinuousCohomology.coeffMap (TopRep.restrictScalarsInt.map Fhom) 0 := by
    have key : ∀ {A B : TopRep ℤ (Field.absoluteGaloisGroup F)}
        (hA : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) X.V = A)
        (hB : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) Y.V = B)
        (g : ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) X.V ⟶
          ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) Y.V)
        (g' : A ⟶ B), g ≫ eqToHom hB = eqToHom hA ≫ g' →
        TauCeti.ContinuousCohomology.coeffMap g 0 ≫ eqToHom (congrArg (continuousCohomology 0) hB) =
          eqToHom (congrArg (continuousCohomology 0) hA) ≫
            TauCeti.ContinuousCohomology.coeffMap g' 0 := by
      rintro A B rfl rfl g g' hg
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hg ⊢
      rw [hg]
    exact key _ _ Fint (TopRep.restrictScalarsInt.map Fhom) hcomm
  have hsqHom :
      (ofDiscreteModuleRestrictScalarsIntIso X 0).hom ≫
          TopModuleCat.restrictScalarsInt.map (TauCeti.ContinuousCohomology.coeffMap Fhom 0) =
        TauCeti.ContinuousCohomology.coeffMap Fint 0 ≫
          (ofDiscreteModuleRestrictScalarsIntIso Y 0).hom := by
    rw [ofDiscreteModuleRestrictScalarsIntIso_hom, ofDiscreteModuleRestrictScalarsIntIso_hom,
      Category.assoc, ← coeffMap_comp_restrictScalarsIntIso_hom (n := 0) Fhom,
      ← Category.assoc, ← hcoeffEq, Category.assoc]
  let z : H0 (Field.absoluteGaloisGroup F) X.V :=
    explicitMap0 (AbsoluteGaloisGroup F) M
      (absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
      (galRepOfZModModuleEquiv n F M).toAddMonoidHom
      (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
        (TopRep.distribMulAction_smul _ g _).symm) x
  have hsq :
      TauCeti.ContinuousCohomology.coeffMap Fhom 0
          (ofDiscreteModuleRestrictScalarsIntEquiv X 0
            ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) X.V).hom z)) =
        ofDiscreteModuleRestrictScalarsIntEquiv Y 0
          (TauCeti.ContinuousCohomology.coeffMap Fint 0
            ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) X.V).hom z)) := by
    have hL : ∀ w, ofDiscreteModuleRestrictScalarsIntEquiv X 0 w =
        (ofDiscreteModuleRestrictScalarsIntIso X 0).hom w := fun w ↦ by
      rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply, restrictScalarsIntEquiv_apply,
        ofDiscreteModuleRestrictScalarsIntIso_hom, CategoryTheory.comp_apply]
    have hR : ∀ w, ofDiscreteModuleRestrictScalarsIntEquiv Y 0 w =
        (ofDiscreteModuleRestrictScalarsIntIso Y 0).hom w := fun w ↦ by
      rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply, restrictScalarsIntEquiv_apply,
        ofDiscreteModuleRestrictScalarsIntIso_hom, CategoryTheory.comp_apply]
    rw [hL, hR]
    exact congr($hsqHom ((explicitH0IsoContinuousCohomology
      (Field.absoluteGaloisGroup F) X.V).hom z))
  rw [galRepOfZModModuleH0Equiv_apply, galRepOfZModModuleH0Equiv_apply]
  change TauCeti.ContinuousCohomology.coeffMap Fhom 0
      (ofDiscreteModuleRestrictScalarsIntEquiv X 0
        ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) X.V).hom z)) = _
  rw [hsq, explicitH0Iso_coeffMap (Field.absoluteGaloisGroup F) X.V Y.V fGal z]
  refine congrArg (ofDiscreteModuleRestrictScalarsIntEquiv Y 0)
    (congrArg (explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) Y.V).hom ?_)
  apply Subtype.ext
  erw [coe_explicitCoeff0, coe_explicitMap0, coe_explicitMap0, coe_explicitCoeff0]
  rfl

section Smooth

variable [ContinuousSMul (AbsoluteGaloisGroup F) M] [ContinuousSMul (AbsoluteGaloisGroup F) N]

/-- **Degree-one naturality of `galRepOfZModModuleH1Equiv`**: the degree-one comparison carries
`explicitCoeff1` to `TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 1`. -/
theorem galRepOfZModModuleH1Equiv_coeffMap
    (f : M →+[AbsoluteGaloisGroup F] N) (x : H1 (AbsoluteGaloisGroup F) M) :
    TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 1
        (galRepOfZModModuleH1Equiv n F M x) =
      galRepOfZModModuleH1Equiv n F N
        (explicitCoeff1 (AbsoluteGaloisGroup F) M f continuous_of_discreteTopology x) := by
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul (ZMod n) N := ⟨continuous_of_discreteTopology⟩
  let fV : (galRepOfZModModule n F M).V →+ (galRepOfZModModule n F N).V :=
    ((galRepOfZModModuleEquiv n F N).toAddMonoidHom.comp f.toAddMonoidHom).comp
      (galRepOfZModModuleEquiv n F M).symm.toAddMonoidHom
  have hf : ∀ (g : Field.absoluteGaloisGroup F) (m : (galRepOfZModModule n F M).V),
      fV ((ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) g • m) =
        g • fV m := fun g m ↦ by
    let m₀ : M := (galRepOfZModModuleEquiv n F M).symm m
    have hm : g • m =
        galRepOfZModModuleEquiv n F M (absoluteGaloisGroupRestrictEquiv F g • m₀) :=
      (TopRep.distribMulAction_smul (galRepOfZModModule n F M) g m).trans
        (galRepOfZModModuleEquiv_smul n F M g m₀).symm
    have hm' : g • galRepOfZModModuleEquiv n F N (f m₀) =
        galRepOfZModModuleEquiv n F N (absoluteGaloisGroupRestrictEquiv F g • f m₀) :=
      (TopRep.distribMulAction_smul (galRepOfZModModule n F N) g _).trans
        (galRepOfZModModuleEquiv_smul n F N g (f m₀)).symm
    change fV (g • m) = g • galRepOfZModModuleEquiv n F N (f m₀)
    rw [hm, hm']
    exact congrArg (galRepOfZModModuleEquiv n F N)
      (map_smul f (absoluteGaloisGroupRestrictEquiv F g) m₀)
  let Fhom : galRepOfZModModule n F M ⟶ galRepOfZModModule n F N := galRepOfZModModuleMap n F f
  have h1 := (galRepOfZModModule n F M).explicitH1AddEquivContinuousCohomologyOfDiscrete_map
    (galRepOfZModModule n F N) (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
    Fhom fV (fun _ ↦ rfl) hf
    (explicitMap1 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
      (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
        (TopRep.distribMulAction_smul _ g _).symm) x)
  rw [galRepOfZModModuleH1Equiv_apply, galRepOfZModModuleH1Equiv_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  refine h1.trans ?_
  refine congrArg (galRepOfZModModule n F N).explicitH1AddEquivContinuousCohomologyOfDiscrete ?_
  rw [explicitCoeff1_eq_explicitMap1, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]
  have hcL := (explicitMap1_comp (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
    (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
    (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) fV continuous_of_discreteTopology
    hf).symm
  have hcR := (explicitMap1_comp (AbsoluteGaloisGroup F) M (AbsoluteGaloisGroup F) N
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) f.toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ map_smul f g m) (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (absoluteGaloisGroupRestrictEquiv F) (galRepOfZModModuleEquiv n F N).toAddMonoidHom
    continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F N g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)).symm
  exact DFunLike.congr_fun
    (hcL.trans ((explicitMap1_congr_of_eq (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F N).V _ _ _ _ rfl rfl).trans hcR.symm)) x

/-- **Degree-two naturality of `galRepOfZModModuleH2Equiv`**: the degree-two comparison carries
`explicitCoeff2` to `TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 2`. -/
theorem galRepOfZModModuleH2Equiv_coeffMap
    (f : M →+[AbsoluteGaloisGroup F] N) (x : H2 (AbsoluteGaloisGroup F) M) :
    TauCeti.ContinuousCohomology.coeffMap (galRepOfZModModuleMap n F f) 2
        (galRepOfZModModuleH2Equiv n F M x) =
      galRepOfZModModuleH2Equiv n F N
        (explicitCoeff2 (AbsoluteGaloisGroup F) M f continuous_of_discreteTopology x) := by
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul (ZMod n) N := ⟨continuous_of_discreteTopology⟩
  let fV : (galRepOfZModModule n F M).V →+ (galRepOfZModModule n F N).V :=
    ((galRepOfZModModuleEquiv n F N).toAddMonoidHom.comp f.toAddMonoidHom).comp
      (galRepOfZModModuleEquiv n F M).symm.toAddMonoidHom
  have hf : ∀ (g : Field.absoluteGaloisGroup F) (m : (galRepOfZModModule n F M).V),
      fV ((ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) g • m) =
        g • fV m := fun g m ↦ by
    let m₀ : M := (galRepOfZModModuleEquiv n F M).symm m
    have hm : g • m =
        galRepOfZModModuleEquiv n F M (absoluteGaloisGroupRestrictEquiv F g • m₀) :=
      (TopRep.distribMulAction_smul (galRepOfZModModule n F M) g m).trans
        (galRepOfZModModuleEquiv_smul n F M g m₀).symm
    have hm' : g • galRepOfZModModuleEquiv n F N (f m₀) =
        galRepOfZModModuleEquiv n F N (absoluteGaloisGroupRestrictEquiv F g • f m₀) :=
      (TopRep.distribMulAction_smul (galRepOfZModModule n F N) g _).trans
        (galRepOfZModModuleEquiv_smul n F N g (f m₀)).symm
    change fV (g • m) = g • galRepOfZModModuleEquiv n F N (f m₀)
    rw [hm, hm']
    exact congrArg (galRepOfZModModuleEquiv n F N)
      (map_smul f (absoluteGaloisGroupRestrictEquiv F g) m₀)
  let Fhom : galRepOfZModModule n F M ⟶ galRepOfZModModule n F N := galRepOfZModModuleMap n F f
  have h2 := (galRepOfZModModule n F M).explicitH2AddEquivContinuousCohomologyOfDiscrete_map
    (galRepOfZModModule n F N) (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
    Fhom fV (fun _ ↦ rfl) hf
    (explicitMap2 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
      (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
        (TopRep.distribMulAction_smul _ g _).symm) x)
  rw [galRepOfZModModuleH2Equiv_apply, galRepOfZModModuleH2Equiv_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  refine h2.trans ?_
  refine congrArg (galRepOfZModModule n F N).explicitH2AddEquivContinuousCohomologyOfDiscrete ?_
  rw [explicitCoeff2_eq_explicitMap2, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]
  have hcL := (explicitMap2_comp (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
    (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
    (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) fV continuous_of_discreteTopology
    hf).symm
  have hcR := (explicitMap2_comp (AbsoluteGaloisGroup F) M (AbsoluteGaloisGroup F) N
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) f.toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ map_smul f g m) (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (absoluteGaloisGroupRestrictEquiv F) (galRepOfZModModuleEquiv n F N).toAddMonoidHom
    continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F N g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)).symm
  exact DFunLike.congr_fun
    (hcL.trans ((explicitMap2_congr_of_eq (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F N).V _ _ _ _ rfl rfl).trans hcR.symm)) x

end Smooth

end ZModModuleMap

end TauCeti
