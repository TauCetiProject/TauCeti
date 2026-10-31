/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Differential
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# The differentiated rational Weyl modules are the irreducible `𝔤𝔩ₙ`-modules

A rational representation `ρ` of `GL n ℂ` differentiates to a representation
`dρ = TauCeti.IsRationalRep.differential` of the matrix Lie algebra `𝔤𝔩ₙ(ℂ)`. On the Lie algebra
side the irreducible finite-dimensional module of a dominant weight `μ` is named:
`TauCeti.glIrreducible n μ`. This file identifies the two sides.

* An irreducible rational representation with a highest weight vector of dominant weight `λ`
  differentiates to `glIrreducible n λ`
  (`TauCeti.IsRationalRep.nonempty_lieModuleEquiv_glIrreducible`). Through the differential the
  representation stays irreducible (`TauCeti.IsRationalRep.isIrreducible_differential`) and the
  highest weight vector stays a highest weight vector of the same weight
  (`TauCeti.IsRationalRep.isGlHighestWeightVector_differential`); an irreducible `𝔤𝔩ₙ`-module with
  a highest weight vector of weight `λ` is `glIrreducible n λ`
  (`TauCeti.nonempty_lieModuleEquiv_glIrreducible`).
* In particular the rational Weyl module `V_λ = TauCeti.rationalWeylRep ℂ n λ` of every dominant
  weight `λ` differentiates to `glIrreducible n λ`
  (`TauCeti.nonempty_lieModuleEquiv_rationalWeylRep_glIrreducible`); for a weight with vanishing
  last entry, `V_λ` is the Weyl module of the Young diagram `λ`.
* Since the differential of a tensor product is the tensor product of the differentials
  (`TauCeti.IsRationalRep.differential_tprod`, `TauCeti.IsRationalRep.tprodLieModuleEquiv`), the
  tensor product `V_λ ⊗ V_μ` differentiates to `glIrreducible n λ ⊗ glIrreducible n μ`
  (`TauCeti.nonempty_lieModuleEquiv_tprod_rationalWeylRep_glIrreducible`). Decompositions of
  tensor products of rational Weyl modules therefore transfer to the named `𝔤𝔩ₙ`-irreducibles.

Only dominant weights with integer entries arise here. The other dominant weights of `𝔤𝔩ₙ`,
which differ from these by a non-integral shift along the central direction, are not considered.

## Implementation notes

The carrier of `V_λ` is a submodule, whose additive monoid structure is the submodule's own. The
differential `TauCeti.IsRationalRep.differential` is stated for representations on additive
groups, and its endomorphisms form a ring only over an additive group. The statements below
therefore first name the additive group structure of the carrier (`letI ... := inferInstance`),
so that the carrier, its endomorphisms and its tensor products elaborate with additive structures
built from it.

## Main results

* `TauCeti.IsRationalRep.nonempty_lieModuleEquiv_glIrreducible`: an irreducible rational
  representation differentiates to the named irreducible `𝔤𝔩ₙ`-module of its highest weight.
* `TauCeti.nonempty_lieModuleEquiv_rationalWeylRep_glIrreducible`: the rational Weyl module of a
  dominant weight `λ` differentiates to `glIrreducible n λ`.
* `TauCeti.nonempty_lieModuleEquiv_tprod_rationalWeylRep_glIrreducible`: the tensor product of
  two rational Weyl modules differentiates to the tensor product of the named irreducibles.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lectures 8 and 15.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, Chapter 7.
-/

public section

open TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : ℕ}

namespace IsRationalRep

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **An irreducible rational representation differentiates to the named irreducible
`𝔤𝔩ₙ`-module of its highest weight**: if `ρ` is irreducible and has a highest weight vector of
dominant weight `λ` (a nonzero vector of weight `λ` fixed by every transvection `xᵢⱼ(c)` with
`i < j`), then `W` with the action of `𝔤𝔩ₙ(ℂ)` through `dρ` is isomorphic to
`glIrreducible n λ`. -/
theorem nonempty_lieModuleEquiv_glIrreducible (hρ : IsRationalRep ρ) [ρ.IsIrreducible]
    {l : DominantWeight n} {w : W} (hw0 : w ≠ 0) (hwl : w ∈ weightSpace ρ l.1)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) w = w) :
    letI := LieRingModule.compLieHom W hρ.differential
    Nonempty (W ≃ₗ⁅ℂ,Matrix (Fin n) (Fin n) ℂ⁆ glIrreducible n fun i ↦ (l.1 i : ℂ)) := by
  let _ := LieRingModule.compLieHom W hρ.differential
  have _ := LieModule.compLieHom W hρ.differential
  have _ := hρ.isIrreducible_differential
  exact TauCeti.nonempty_lieModuleEquiv_glIrreducible (isGlDominantIntegral_intCast l.antitone)
    (hρ.isGlHighestWeightVector_differential hw0 hwl hw)

end IsRationalRep

/-- **The rational Weyl module of a dominant weight `λ` differentiates to `glIrreducible n λ`**:
`V_λ`, with the action of `𝔤𝔩ₙ(ℂ)` through the differential of `TauCeti.rationalWeylRep ℂ n λ`, is
isomorphic to the named irreducible `𝔤𝔩ₙ`-module of highest weight `λ`. -/
theorem nonempty_lieModuleEquiv_rationalWeylRep_glIrreducible (l : DominantWeight n) :
    letI : AddCommGroup (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule := inferInstance
    letI := LieRingModule.compLieHom (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule
      (isRationalRep_rationalWeylRep n l).differential
    Nonempty ((weylModuleOfShape ℂ n l.detShiftShape).toSubmodule ≃ₗ⁅ℂ,Matrix (Fin n) (Fin n) ℂ⁆
      glIrreducible n fun i ↦ (l.1 i : ℂ)) := by
  obtain ⟨v, hvl, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (weightSpace_rationalWeylRep_self_ne_bot ℂ l)
  exact (isRationalRep_rationalWeylRep n l).nonempty_lieModuleEquiv_glIrreducible hv0 hvl
    fun _ _ hij ↦ rationalWeylRep_apply_transvectionUnit_eq_self l hij hvl

/-- **The tensor product of two rational Weyl modules differentiates to the tensor product of the
named irreducibles**: `V_λ ⊗ V_μ`, with the action of `𝔤𝔩ₙ(ℂ)` through the differential of the
tensor product representation, is isomorphic to `glIrreducible n λ ⊗ glIrreducible n μ` with its
tensor product `𝔤𝔩ₙ`-module structure. -/
theorem nonempty_lieModuleEquiv_tprod_rationalWeylRep_glIrreducible (l m : DominantWeight n) :
    letI : AddCommGroup (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule := inferInstance
    letI : AddCommGroup (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule := inferInstance
    letI := LieRingModule.compLieHom
      ((weylModuleOfShape ℂ n l.detShiftShape).toSubmodule ⊗[ℂ]
        (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
      ((isRationalRep_rationalWeylRep n l).tprod (isRationalRep_rationalWeylRep n m)).differential
    Nonempty ((weylModuleOfShape ℂ n l.detShiftShape).toSubmodule ⊗[ℂ]
        (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule ≃ₗ⁅ℂ,Matrix (Fin n) (Fin n) ℂ⁆
      (glIrreducible n fun i ↦ (l.1 i : ℂ)) ⊗[ℂ] glIrreducible n fun i ↦ (m.1 i : ℂ)) := by
  obtain ⟨e₁⟩ := nonempty_lieModuleEquiv_rationalWeylRep_glIrreducible l
  obtain ⟨e₂⟩ := nonempty_lieModuleEquiv_rationalWeylRep_glIrreducible m
  exact ⟨(isRationalRep_rationalWeylRep n l).tprodLieModuleEquiv
    (isRationalRep_rationalWeylRep n m) e₁ e₂⟩

end TauCeti
