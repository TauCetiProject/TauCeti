/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso

/-!
# Discrete Galois modules as `GalRep n F` objects

Local class field theory states its finiteness and Euler-characteristic theorems for bundled
representations `A : TauCeti.ClassFieldTheory.GalRep n F`, that is, objects of
`TopRep (ZMod n) (Field.absoluteGaloisGroup F)` with Mathlib's `continuousCohomology`. Arithmetic
applications—such as elliptic-curve torsion, Kummer modules, and unramified local duality—instead
work with unbundled discrete `AbsoluteGaloisGroup F`-modules `M` killed by `n` and explicit
low-degree cohomology `H⁰`, `H¹`, `H²`.

This file builds the general bridge between the two for an arbitrary field `F`:

* `TauCeti.ClassFieldTheory.galRepOfDiscreteModule`: equips `M` with its `ZMod n`-module structure
  and restricts the Galois action along `TauCeti.absoluteGaloisGroupRestrictEquiv F` to obtain an
  object of `GalRep n F`.
* `TauCeti.ClassFieldTheory.galRepOfDiscreteModuleEquiv`: the underlying additive equivalence
  `M ≃+ (galRepOfDiscreteModule n F M hM).V`, intertwining the Galois actions
  (`galRepOfDiscreteModuleEquiv_smul`).
* `TauCeti.ClassFieldTheory.galRepOfDiscreteModuleH0Equiv`, `galRepOfDiscreteModuleH1Equiv`, and
  `galRepOfDiscreteModuleH2Equiv`: additive equivalences identifying explicit `Hⁱ(G_F, M)` with
  `continuousCohomology i (galRepOfDiscreteModule n F M hM)` for `i = 0, 1, 2`.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

universe u

variable (n : ℕ) (F : Type u) [Field F]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup F) M] [ContinuousSMul (AbsoluteGaloisGroup F) M]
  (hM : ∀ x : M, n • x = 0)

/-- **Bundle an unbundled discrete `G_F`-module killed by `n` as an object of `GalRep n F`**,
equipping `M` with its `ZMod n`-module structure and restricting the Galois action along
`TauCeti.absoluteGaloisGroupRestrictEquiv F`. -/
def galRepOfDiscreteModule : GalRep n F :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  haveI : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
    (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) M)

/-- `galRepOfDiscreteModule n F M hM` is smooth and discrete. -/
theorem isSmoothDiscrete_galRepOfDiscreteModule :
    IsSmoothDiscrete (ZMod n) (galRepOfDiscreteModule n F M hM) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (ofDiscreteModule_isSmoothDiscrete (ZMod n) (AbsoluteGaloisGroup F) M).res
    (absoluteGaloisGroupRestrictEquiv F).continuous

/-- The carrier of `galRepOfDiscreteModule n F M hM` has the discrete topology. -/
instance : DiscreteTopology (galRepOfDiscreteModule n F M hM).V :=
  (isSmoothDiscrete_galRepOfDiscreteModule n F M hM).discreteTopology

/-- `Fact` instance for `isSmoothDiscrete_galRepOfDiscreteModule`. -/
instance : Fact (IsSmoothDiscrete (ZMod n) (galRepOfDiscreteModule n F M hM)) :=
  ⟨isSmoothDiscrete_galRepOfDiscreteModule n F M hM⟩

attribute [local instance] TopRep.distribMulAction

/-- The action of `Field.absoluteGaloisGroup F` on `galRepOfDiscreteModule n F M hM` is
continuous. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup F) (galRepOfDiscreteModule n F M hM).V :=
  (isSmoothDiscrete_galRepOfDiscreteModule n F M hM).continuousSMul

/-- The coefficient dictionary `M ≃+ (galRepOfDiscreteModule n F M hM).V`. -/
def galRepOfDiscreteModuleEquiv : M ≃+ (galRepOfDiscreteModule n F M hM).V :=
  AddEquiv.refl M

/-- Finiteness of `(galRepOfDiscreteModule n F M hM).V` when `M` is finite. -/
instance [Finite M] : Finite (galRepOfDiscreteModule n F M hM).V :=
  Finite.of_equiv M (galRepOfDiscreteModuleEquiv n F M hM).toEquiv

omit [ContinuousSMul (AbsoluteGaloisGroup F) M] in
/-- **The coefficient dictionary is equivariant**: `g ∈ Field.absoluteGaloisGroup F` acts on
`galRepOfDiscreteModule n F M hM` as its restriction to the separable closure acts on `M`. -/
@[simp]
theorem galRepOfDiscreteModuleEquiv_smul (g : Field.absoluteGaloisGroup F) (x : M) :
    galRepOfDiscreteModuleEquiv n F M hM (absoluteGaloisGroupRestrictEquiv F g • x) =
      (galRepOfDiscreteModule n F M hM).ρ g (galRepOfDiscreteModuleEquiv n F M hM x) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (ofDiscreteModule_ρ_apply_apply (R := ZMod n)
      (absoluteGaloisGroupRestrictEquiv F g) x).symm.trans
    (ContRepresentation.restrict_apply_apply
      (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup F) M).ρ
      (absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F) g x).symm

/-- **Degree-zero cohomology comparison** between explicit `H⁰(G_F, M)` and
`continuousCohomology 0 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH0Equiv :
    H0 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 0 (galRepOfDiscreteModule n F M hM) :=
  ((AddEquiv.ofBijective
      (explicitMap0 (AbsoluteGaloisGroup F) M
        (absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (galRepOfDiscreteModuleEquiv n F M hM).toAddMonoidHom
        fun g x ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g x).trans
          (TopRep.distribMulAction_smul _ g _).symm)
      (explicitMap0_bijective (AbsoluteGaloisGroup F) M
        (absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (absoluteGaloisGroupRestrictEquiv F).surjective
        (galRepOfDiscreteModuleEquiv n F M hM).toAddMonoidHom
        (galRepOfDiscreteModuleEquiv n F M hM).bijective
        fun g x ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g x).trans
          (TopRep.distribMulAction_smul _ g _).symm)).trans
    (explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F)
      (galRepOfDiscreteModule n F M hM).V).toContinuousLinearEquiv.toAddEquiv).trans
    (ofDiscreteModuleRestrictScalarsIntEquiv (galRepOfDiscreteModule n F M hM) 0)

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
              (TopRep.distribMulAction_smul _ g _).symm) x)) :=
  (rfl)

/-- **Degree-one cohomology comparison** between explicit `H¹(G_F, M)` and
`continuousCohomology 1 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH1Equiv :
    H1 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 1 (galRepOfDiscreteModule n F M hM) :=
  (explicitMap1Equiv (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfDiscreteModule n F M hM).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfDiscreteModuleEquiv n F M hM) continuous_of_discreteTopology
      continuous_of_discreteTopology
      fun g x ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans
    (galRepOfDiscreteModule n F M hM).explicitH1AddEquivContinuousCohomologyOfDiscrete

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
  rw [galRepOfDiscreteModuleH1Equiv, AddEquiv.trans_apply, explicitMap1Equiv_apply]

/-- **Degree-two cohomology comparison** between explicit `H²(G_F, M)` and
`continuousCohomology 2 (galRepOfDiscreteModule n F M hM)`. -/
def galRepOfDiscreteModuleH2Equiv :
    H2 (AbsoluteGaloisGroup F) M ≃+ continuousCohomology 2 (galRepOfDiscreteModule n F M hM) :=
  (explicitMap2Equiv (AbsoluteGaloisGroup F) M (Field.absoluteGaloisGroup F)
      (galRepOfDiscreteModule n F M hM).V (absoluteGaloisGroupRestrictEquiv F)
      (galRepOfDiscreteModuleEquiv n F M hM) continuous_of_discreteTopology
      continuous_of_discreteTopology
      fun g x ↦ (galRepOfDiscreteModuleEquiv_smul n F M hM g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans
    (galRepOfDiscreteModule n F M hM).explicitH2AddEquivContinuousCohomologyOfDiscrete

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
  rw [galRepOfDiscreteModuleH2Equiv, AddEquiv.trans_apply, explicitMap2Equiv_apply]

end TauCeti.ClassFieldTheory
