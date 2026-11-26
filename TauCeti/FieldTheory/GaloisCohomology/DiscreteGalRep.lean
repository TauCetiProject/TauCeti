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
            (galRepOfZModModule n F M).V).hom
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

private theorem galRepOfZModModuleEquiv_symm_smul (g : Field.absoluteGaloisGroup F)
    (m : (galRepOfZModModule n F M).V) :
    (galRepOfZModModuleEquiv n F M).symm (g • m) =
      absoluteGaloisGroupRestrictEquiv F g • (galRepOfZModModuleEquiv n F M).symm m := by
  apply (galRepOfZModModuleEquiv n F M).injective
  rw [AddEquiv.apply_symm_apply, galRepOfZModModuleEquiv_smul, TopRep.distribMulAction_smul,
    AddEquiv.apply_symm_apply]

/-- Transport an equivariant map `M →+[AbsoluteGaloisGroup F] N` across
`galRepOfZModModuleEquiv` to an equivariant map between the carriers of
`galRepOfZModModule`. -/
private def galRepOfZModModuleTransport (f : M →+[AbsoluteGaloisGroup F] N) :
    (galRepOfZModModule n F M).V →+[Field.absoluteGaloisGroup F]
      (galRepOfZModModule n F N).V where
  toAddMonoidHom :=
    ((galRepOfZModModuleEquiv n F N).toAddMonoidHom.comp f.toAddMonoidHom).comp
      (galRepOfZModModuleEquiv n F M).symm.toAddMonoidHom
  map_smul' g m := by
    simp only [AddMonoidHom.toFun_eq_coe, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      MonoidHom.id_apply]
    rw [galRepOfZModModuleEquiv_symm_smul]
    exact (congrArg (galRepOfZModModuleEquiv n F N)
        (f.map_smul (absoluteGaloisGroupRestrictEquiv F g)
          ((galRepOfZModModuleEquiv n F M).symm m))).trans
      ((galRepOfZModModuleEquiv_smul n F N g _).trans (TopRep.distribMulAction_smul _ g _).symm)

/-- `galRepOfZModModuleTransport` intertwines the coefficient dictionaries
`galRepOfZModModuleEquiv`. -/
private theorem galRepOfZModModuleTransport_galRepOfZModModuleEquiv
    (f : M →+[AbsoluteGaloisGroup F] N) (m : M) :
    galRepOfZModModuleTransport n F f (galRepOfZModModuleEquiv n F M m) =
      galRepOfZModModuleEquiv n F N (f m) :=
  congrArg (fun z ↦ galRepOfZModModuleEquiv n F N (f z))
    ((galRepOfZModModuleEquiv n F M).symm_apply_apply m)

/-- **Bundle an equivariant additive homomorphism of discrete `ZMod n[G_F]`-modules as a morphism
in `GalRep n F`.** -/
def galRepOfZModModuleMap (f : M →+[AbsoluteGaloisGroup F] N) :
    galRepOfZModModule n F M ⟶ galRepOfZModModule n F N :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨f.toAddMonoidHom.toZModLinearMap n, continuous_of_discreteTopology⟩
      isIntertwining' g := ContinuousLinearMap.ext fun m : (galRepOfZModModule n F M).V ↦ by
        have h := map_smul (galRepOfZModModuleTransport n F f) g m
        rw [TopRep.distribMulAction_smul, TopRep.distribMulAction_smul] at h
        exact h }

/-- `galRepOfZModModuleMap` intertwines the coefficient dictionaries `galRepOfZModModuleEquiv`. -/
@[simp]
theorem galRepOfZModModuleMap_hom_galRepOfZModModuleEquiv
    (f : M →+[AbsoluteGaloisGroup F] N) (m : M) :
    (galRepOfZModModuleMap n F f).hom (galRepOfZModModuleEquiv n F M m) =
      galRepOfZModModuleEquiv n F N (f m) :=
  galRepOfZModModuleTransport_galRepOfZModModuleEquiv n F f m

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
  -- Three-step transport:
  -- 1. Unfold `galRepOfZModModuleH0Equiv` and push `coeffMap` past scalar restriction.
  -- 2. Push `coeffMap` past `explicitH0IsoContinuousCohomology` via `explicitH0Iso_coeffMap`.
  -- 3. Identify `explicitCoeff0` on the transported carrier with `explicitCoeff0` on `M`.
  let fGal := galRepOfZModModuleTransport n F f
  let Fint := ofDiscreteModuleMap fGal.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul fGal g m
  have hf : ∀ m, Fint.hom m = (galRepOfZModModuleMap n F f).hom m := fun m ↦
    ofDiscreteModuleMap_hom_apply fGal.toAddMonoidHom.toIntLinearMap
      (fun g x ↦ map_smul fGal g x) m
  rw [galRepOfZModModuleH0Equiv_apply, galRepOfZModModuleH0Equiv_apply,
    ofDiscreteModuleRestrictScalarsIntEquiv_coeffMap (galRepOfZModModuleMap n F f) Fint hf 0,
    explicitH0Iso_coeffMap (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (galRepOfZModModule n F N).V fGal]
  refine congrArg (ofDiscreteModuleRestrictScalarsIntEquiv (galRepOfZModModule n F N) 0)
    (congrArg (explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F N).V).hom (Subtype.ext ?_))
  rw [coe_explicitCoeff0]
  refine (congrArg fGal (coe_explicitMap0 _ _ _ _ _ x)).trans ?_
  dsimp only [fGal]
  rw [AddEquiv.coe_toAddMonoidHom, galRepOfZModModuleTransport_galRepOfZModModuleEquiv,
    ← coe_explicitCoeff0 (AbsoluteGaloisGroup F) M f x]
  exact (coe_explicitMap0 (AbsoluteGaloisGroup F) N
    (H := Field.absoluteGaloisGroup F) (N := (galRepOfZModModule n F N).V)
    (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
    (galRepOfZModModuleEquiv n F N).toAddMonoidHom _
    (explicitCoeff0 (AbsoluteGaloisGroup F) M f x)).symm

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
  let fGal := galRepOfZModModuleTransport n F f
  let Fhom : galRepOfZModModule n F M ⟶ galRepOfZModModule n F N := galRepOfZModModuleMap n F f
  have h1 := (galRepOfZModModule n F M).explicitH1AddEquivContinuousCohomologyOfDiscrete_map
    (galRepOfZModModule n F N) (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
    Fhom fGal.toAddMonoidHom (fun _ ↦ rfl) (fun g m ↦ map_smul fGal g m)
    (explicitMap1 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
      (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
        (TopRep.distribMulAction_smul _ g _).symm) x)
  rw [galRepOfZModModuleH1Equiv_apply, galRepOfZModModuleH1Equiv_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  refine h1.trans
    (congrArg (galRepOfZModModule n F N).explicitH1AddEquivContinuousCohomologyOfDiscrete ?_)
  rw [explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq (AbsoluteGaloisGroup F) M
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F M).V
    (absoluteGaloisGroupRestrictEquiv F) (galRepOfZModModuleEquiv n F M).toAddMonoidHom
    continuous_of_discreteTopology _
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) fGal.toAddMonoidHom
    continuous_of_discreteTopology (fun g m ↦ map_smul fGal g m)
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) f.toAddMonoidHom
    continuous_of_discreteTopology (fun g m ↦ map_smul f g m)
    (absoluteGaloisGroupRestrictEquiv F) (galRepOfZModModuleEquiv n F N).toAddMonoidHom
    continuous_of_discreteTopology _
    rfl (AddMonoidHom.ext fun m ↦ galRepOfZModModuleTransport_galRepOfZModModuleEquiv n F f m) x

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
  let fGal := galRepOfZModModuleTransport n F f
  let Fhom : galRepOfZModModule n F M ⟶ galRepOfZModModule n F N := galRepOfZModModuleMap n F f
  have h2 := (galRepOfZModModule n F M).explicitH2AddEquivContinuousCohomologyOfDiscrete_map
    (galRepOfZModModule n F N) (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
    Fhom fGal.toAddMonoidHom (fun _ ↦ rfl) (fun g m ↦ map_smul fGal g m)
    (explicitMap2 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
      (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
        (TopRep.distribMulAction_smul _ g _).symm) x)
  rw [galRepOfZModModuleH2Equiv_apply, galRepOfZModModuleH2Equiv_apply,
    TauCeti.ContinuousCohomology.coeffMap_def]
  refine h2.trans
    (congrArg (galRepOfZModModule n F N).explicitH2AddEquivContinuousCohomologyOfDiscrete ?_)
  rw [explicitCoeff2_eq_explicitMap2, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]
  have hcL := (explicitMap2_comp (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
    (galRepOfZModModule n F M).V (absoluteGaloisGroupRestrictEquiv F)
    (galRepOfZModModuleEquiv n F M).toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F M g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) fGal.toAddMonoidHom
    continuous_of_discreteTopology (fun g m ↦ map_smul fGal g m)).symm
  have hcR := (explicitMap2_comp (AbsoluteGaloisGroup F) M (AbsoluteGaloisGroup F) N
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) f.toAddMonoidHom
    continuous_of_discreteTopology (fun g m ↦ map_smul f g m)
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V
    (absoluteGaloisGroupRestrictEquiv F) (galRepOfZModModuleEquiv n F N).toAddMonoidHom
    continuous_of_discreteTopology
    (fun g m ↦ (galRepOfZModModuleEquiv_smul n F N g m).trans
      (TopRep.distribMulAction_smul _ g _).symm)).symm
  exact DFunLike.congr_fun (hcL.trans ((explicitMap2_congr_of_eq (AbsoluteGaloisGroup F) M
    (Field.absoluteGaloisGroup F) (galRepOfZModModule n F N).V _ _ _ _ rfl
    (AddMonoidHom.ext fun m ↦ galRepOfZModModuleTransport_galRepOfZModModuleEquiv n F f m)).trans
      hcR.symm)) x

end Smooth

end ZModModuleMap

end TauCeti
