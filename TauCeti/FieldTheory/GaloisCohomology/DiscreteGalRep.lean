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
`M` (either already equipped with a `Module (ZMod n) M` instance or merely killed by `n`) and
explicit low-degree cohomology `H⁰`, `H¹`, `H²`.

This file builds the shared bridge between the two for an arbitrary field `F`:

* `TauCeti.GalRep`: `TopRep (ZMod n) (Field.absoluteGaloisGroup F)`.
* `TauCeti.galRepOfZModModule`: restricts the Galois action on a discrete `ZMod n`-module `M` along
  `TauCeti.absoluteGaloisGroupRestrictEquiv F` to obtain an object of `GalRep n F`, together with
  `galRepOfZModModuleEquiv`, `galRepOfZModModuleEquiv_smul`, and
  `galRepOfZModModuleH0Equiv` / `H1Equiv` / `H2Equiv`.
* `TauCeti.galRepOfDiscreteModule`: specializes `galRepOfZModModule` to an unbundled discrete
  `AbsoluteGaloisGroup F`-module killed by `n` via `AddCommGroup.zmodModule`, together with
  `galRepOfDiscreteModuleEquiv`, `galRepOfDiscreteModuleEquiv_smul`, and
  `galRepOfDiscreteModuleH0Equiv` / `H1Equiv` / `H2Equiv`.
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

section Unbundled

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup F) M] (hM : ∀ x : M, n • x = 0)

/-- **Bundle an unbundled discrete `G_F`-module killed by `n` as an object of `GalRep n F`**,
equipping `M` with its `ZMod n`-module structure via `AddCommGroup.zmodModule hM` and
delegating to `galRepOfZModModule`. -/
def galRepOfDiscreteModule : GalRep n F :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  galRepOfZModModule n F M

/-- The carrier of `galRepOfDiscreteModule n F M hM` has the discrete topology. -/
instance : DiscreteTopology (galRepOfDiscreteModule n F M hM).V :=
  inferInstanceAs (DiscreteTopology M)

/-- The coefficient dictionary `M ≃+ (galRepOfDiscreteModule n F M hM).V`. -/
def galRepOfDiscreteModuleEquiv : M ≃+ (galRepOfDiscreteModule n F M hM).V :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  galRepOfZModModuleEquiv n F M

/-- Finiteness of `(galRepOfDiscreteModule n F M hM).V` when `M` is finite. -/
instance [Finite M] : Finite (galRepOfDiscreteModule n F M hM).V :=
  Finite.of_equiv M (galRepOfDiscreteModuleEquiv n F M hM).toEquiv

/-- **The coefficient dictionary is equivariant**: `g ∈ Field.absoluteGaloisGroup F` acts on
`galRepOfDiscreteModule n F M hM` as its restriction to the separable closure acts on `M`. -/
@[simp]
theorem galRepOfDiscreteModuleEquiv_smul (g : Field.absoluteGaloisGroup F) (x : M) :
    galRepOfDiscreteModuleEquiv n F M hM (absoluteGaloisGroupRestrictEquiv F g • x) =
      (galRepOfDiscreteModule n F M hM).ρ g (galRepOfDiscreteModuleEquiv n F M hM x) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  exact galRepOfZModModuleEquiv_smul n F M g x

attribute [local instance] TopRep.distribMulAction

/-- **Degree-zero cohomology comparison** between explicit `H⁰(G_F, M)` and
`continuousCohomology 0 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH0Equiv :
    H0 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 0 (galRepOfDiscreteModule n F M hM) :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  galRepOfZModModuleH0Equiv n F M

/-- `galRepOfDiscreteModuleH0Equiv` is pullback along `absoluteGaloisGroupRestrictEquiv F`
followed by the degree-zero comparison with canonical continuous cohomology. -/
theorem galRepOfDiscreteModuleH0Equiv_apply (x : H0 (AbsoluteGaloisGroup F) M) :
    galRepOfDiscreteModuleH0Equiv n F M hM x =
      ofDiscreteModuleRestrictScalarsIntEquiv (galRepOfDiscreteModule n F M hM) 0
        ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F)
            (galRepOfDiscreteModule n F M hM).V).toContinuousLinearEquiv.toAddEquiv
          (explicitMap0 (AbsoluteGaloisGroup F) M
            (absoluteGaloisGroupRestrictEquiv F :
              Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
            (galRepOfDiscreteModuleEquiv n F M hM).toAddMonoidHom
            (fun g m ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g m).trans
              (TopRep.distribMulAction_smul _ g _).symm) x)) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  exact galRepOfZModModuleH0Equiv_apply n F M x

variable [ContinuousSMul (AbsoluteGaloisGroup F) M]

/-- `galRepOfDiscreteModule n F M hM` is smooth and discrete when `G_F` acts continuously on
`M`. -/
theorem isSmoothDiscrete_galRepOfDiscreteModule :
    IsSmoothDiscrete (ZMod n) (galRepOfDiscreteModule n F M hM) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  exact isSmoothDiscrete_galRepOfZModModule n F M

/-- `Fact` instance for `isSmoothDiscrete_galRepOfDiscreteModule`. -/
instance : Fact (IsSmoothDiscrete (ZMod n) (galRepOfDiscreteModule n F M hM)) :=
  ⟨isSmoothDiscrete_galRepOfDiscreteModule n F M hM⟩

/-- The action of `Field.absoluteGaloisGroup F` on `galRepOfDiscreteModule n F M hM` is
continuous. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup F) (galRepOfDiscreteModule n F M hM).V :=
  (isSmoothDiscrete_galRepOfDiscreteModule n F M hM).continuousSMul

/-- **Degree-one cohomology comparison** between explicit `H¹(G_F, M)` and
`continuousCohomology 1 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH1Equiv :
    H1 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 1 (galRepOfDiscreteModule n F M hM) :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  galRepOfZModModuleH1Equiv n F M

/-- `galRepOfDiscreteModuleH1Equiv` is degree-one pullback along
`absoluteGaloisGroupRestrictEquiv F` followed by the comparison with canonical continuous
cohomology. -/
theorem galRepOfDiscreteModuleH1Equiv_apply (x : H1 (AbsoluteGaloisGroup F) M) :
    galRepOfDiscreteModuleH1Equiv n F M hM x =
      (galRepOfDiscreteModule n F M hM).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (explicitMap1 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
          (galRepOfDiscreteModule n F M hM).V (absoluteGaloisGroupRestrictEquiv F)
          (galRepOfDiscreteModuleEquiv n F M hM).toAddMonoidHom continuous_of_discreteTopology
          (fun g m ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g m).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  exact galRepOfZModModuleH1Equiv_apply n F M x

/-- **Degree-two cohomology comparison** between explicit `H²(G_F, M)` and
`continuousCohomology 2 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH2Equiv :
    H2 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 2 (galRepOfDiscreteModule n F M hM) :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  galRepOfZModModuleH2Equiv n F M

/-- `galRepOfDiscreteModuleH2Equiv` is degree-two pullback along
`absoluteGaloisGroupRestrictEquiv F` followed by the comparison with canonical continuous
cohomology. -/
theorem galRepOfDiscreteModuleH2Equiv_apply (x : H2 (AbsoluteGaloisGroup F) M) :
    galRepOfDiscreteModuleH2Equiv n F M hM x =
      (galRepOfDiscreteModule n F M hM).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
          (galRepOfDiscreteModule n F M hM).V (absoluteGaloisGroupRestrictEquiv F)
          (galRepOfDiscreteModuleEquiv n F M hM).toAddMonoidHom continuous_of_discreteTopology
          (fun g m ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g m).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  exact galRepOfZModModuleH2Equiv_apply n F M x

end Unbundled

end TauCeti
