/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Circle.Basic
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalCoefficients
import TauCeti.AlgebraicTopology.ClassifyingSpace.Monodromy
import TauCeti.AlgebraicTopology.Cohomology.Twisted.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic
public import TauCeti.RepresentationTheory.Cyclic.IntSign
public import TauCeti.RepresentationTheory.Homological.GroupHomology.InfiniteCyclic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InfiniteCyclic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Homology and cohomology of the circle with local coefficients

A representation `A` of `ℤ` over a commutative ring `k` gives a local coefficient system on the
circle (`TauCeti.circleLocalSystem A`): the system `TauCeti.classifyingSpaceLocalSystem k A` on
Milnor's classifying space of `ℤ`, pulled back along the homotopy equivalence
`TauCeti.circleHomotopyEquivClassifyingSpace`. On the classifying space this system has monodromy
`A.ρ` (`TauCeti.classifyingSpaceLocalSystem_map_comp_basepointIso`), and the map from the circle
induces the identity of `ℤ` on fundamental groups
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`), so the
monodromy of the pulled back system around the circle is `T = A.ρ (Multiplicative.ofAdd 1)`
(`TauCeti.circleLocalSystem_map_comp_basepointIso`).

A homotopy equivalence induces isomorphisms on homology with local coefficients, and the homology
of the classifying space with these coefficients is group homology, so
`Hₙ(S¹; A) ≅ Hₙ(ℤ, A)` (`TauCeti.circleTwistedHomologyIsoGroupHomology`). The group homology of
the infinite cyclic group (`TauCeti.RepresentationTheory.Homological.GroupHomology.InfiniteCyclic`)
then computes it:

* `H₀(S¹; A) ≅ A / (T - 𝟙) A` (`TauCeti.circleTwistedHomologyIso₀`);
* `H₁(S¹; A) ≅ ker (T - 𝟙)` (`TauCeti.circleTwistedHomologyIso₁`);
* `Hₙ(S¹; A) = 0` for `n ≥ 2` (`TauCeti.isZero_circleTwistedHomology_add_two`).

This agrees with the homology of the cellular complex `A --(T - 𝟙)--> A` of the circle with one
vertex and one edge, whose differential compares the coefficient transported once around the edge
with the coefficient at its start; that cellular comparison is motivation only and is not
formalised here.

For the rank-one integral system of monodromy `-1`, coming from the sign representation
`TauCeti.intSignRep` (`TauCeti.RepresentationTheory.Cyclic.IntSign`), the differential is `-2`.
Its homology is `H₀ = ℤ / 2` (`TauCeti.circleTwistedHomologyIntSignRepIso₀ZMod`), `H₁ = 0`
(`TauCeti.isZero_circleTwistedHomology_one_intSignRep`) and zero above, although the circle with
constant integral coefficients has `H₀ = H₁ = ℤ`: a cycle running twice around the circle has
coefficient `a + (-1) a = 0`. This local system is the orientation system of the Möbius line
bundle over the circle, the simplest nonorientable line bundle; in Morse–Bott homology such
systems are the coefficients carried by critical circles whose negative normal bundle is a Möbius
line.

Dually, the cochains of the circle with coefficients in `circleLocalSystem A` and values in a
`k`-module `N` are the maps from its twisted chains to `N`. A homotopy equivalence also induces
isomorphisms on this cohomology, with no hypothesis on `A`
(`ContinuousMap.HomotopyEquiv.isIso_twistedCohomologyMap`), so it is the group cohomology of `ℤ`
with coefficients in `Homₖ(A, N)` (`TauCeti.circleTwistedCohomologyIsoGroupCohomology`). The
generator acts on `Homₖ(A, N)` through precomposition with `T`, so this is the cohomology of the
dual complex `Homₖ(A, N) --(φ ↦ φ ∘ (T - 𝟙))--> Homₖ(A, N)`:

* `H⁰(S¹; A, N) ≅ {φ | φ ∘ (T - 𝟙) = 0}` (`TauCeti.circleTwistedCohomologyIso₀`);
* `H¹(S¹; A, N) ≅ Homₖ(A, N) / {φ ∘ (T - 𝟙)}` (`TauCeti.circleTwistedCohomologyIso₁`);
* `Hⁿ(S¹; A, N) = 0` for `n ≥ 2` (`TauCeti.isZero_circleTwistedCohomology_add_two`).

For the sign system with values in `ℤ`, precomposition with `T - 𝟙 = -2` is multiplication by
`-2` on `Hom(ℤ, ℤ) ≅ ℤ`, so `H⁰ = 0` (`TauCeti.isZero_circleTwistedCohomology_zero_intSignRep`)
and `H¹ = ℤ / 2` (`TauCeti.circleTwistedCohomologyIntSignRepIso₁ZMod`): the torsion of `H₀`
reappears in `H¹`, as the universal coefficient theorem predicts.

## Main definitions

* `TauCeti.circleLocalSystem`: the local system on the circle of a representation of `ℤ`.
* `TauCeti.circleLocalSystemBasepointIso`: its fibre at the base point is `A`.
* `TauCeti.circleTwistedHomologyIsoGroupHomology`: `Hₙ(S¹; A) ≅ Hₙ(ℤ, A)`.
* `TauCeti.circleTwistedHomologyIso₀`, `TauCeti.circleTwistedHomologyIso₁`: the homology in
  degrees `0` and `1`.
* `TauCeti.circleTwistedHomologyIntSignRepIso₀ZMod`: `H₀(S¹; ℤ⁻) ≅ ℤ / 2`.
* `TauCeti.circleTwistedCohomologyIsoGroupCohomology`: `Hⁿ(S¹; A, N) ≅ Hⁿ(ℤ, Homₖ(A, N))`.
* `TauCeti.circleTwistedCohomologyIso₀`, `TauCeti.circleTwistedCohomologyIso₁`: the cohomology
  in degrees `0` and `1`.
* `TauCeti.circleTwistedCohomologyIntSignRepIso₁ZMod`: `H¹(S¹; ℤ⁻, ℤ) ≅ ℤ / 2`.

## Main results

* `TauCeti.circleLocalSystem_map_comp_basepointIso`: transport around a loop acts through its
  degree.
* `TauCeti.isZero_circleTwistedHomology_add_two`: `Hₙ(S¹; A) = 0` for `n ≥ 2`.
* `TauCeti.isZero_circleTwistedHomology_one_intSignRep`: `H₁(S¹; ℤ⁻) = 0`.
* `TauCeti.isZero_circleTwistedCohomology_add_two`: `Hⁿ(S¹; A, N) = 0` for `n ≥ 2`.
* `TauCeti.isZero_circleTwistedCohomology_zero_intSignRep`: `H⁰(S¹; ℤ⁻, ℤ) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (homology with
  local coefficients, and its cellular computation).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientation local systems of the negative
  bundles in Morse–Bott homology).
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

namespace TauCeti

variable {k : Type} [CommRing k] (A : Rep k (Multiplicative ℤ))

/-- The local coefficient system on the circle associated to a representation `A` of `ℤ`: the
system of `A` on the classifying space of `ℤ`, pulled back to the circle. Its monodromy around the
circle is `A.ρ (Multiplicative.ofAdd 1)` (`TauCeti.circleLocalSystem_map_comp_basepointIso`). -/
abbrev circleLocalSystem : LocalCoefficientSystem k (TopCat.of Circle) :=
  (pullback (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun).hom).obj
    (classifyingSpaceLocalSystem k A)

/-- Identify the fibre of `circleLocalSystem A` at the base point `1` with `A`: the circle's base
point goes to the base point of the classifying space, whose fibre is `A` by
`TauCeti.classifyingSpaceLocalSystemBasepointIso`. -/
def circleLocalSystemBasepointIso :
    (circleLocalSystem A).obj (FundamentalGroupoid.mk 1) ≅ ModuleCat.of k A :=
  eqToIso (show (circleLocalSystem A).obj (FundamentalGroupoid.mk 1) =
      (classifyingSpaceLocalSystem k A).obj
        (FundamentalGroupoid.mk (classifyingSpaceBasepoint (Multiplicative ℤ))) from
    congrArg (classifyingSpaceLocalSystem k A).obj (congrArg FundamentalGroupoid.mk (by simp))) ≪≫
    classifyingSpaceLocalSystemBasepointIso k A

/-- **The monodromy of `circleLocalSystem A`**: under `circleLocalSystemBasepointIso`, transport
around a loop at `1` is the action of its degree, so the loop going once around the circle acts
by `A.ρ (Multiplicative.ofAdd 1)`. -/
@[reassoc]
theorem circleLocalSystem_map_comp_basepointIso (γ : FundamentalGroup Circle 1) :
    (circleLocalSystem A).map γ.asHom ≫ (circleLocalSystemBasepointIso A).hom =
      (circleLocalSystemBasepointIso A).hom ≫
        ModuleCat.ofHom (A.ρ (Circle.fundamentalGroupMulEquiv 1 γ)) := by
  have h : (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun).hom 1 =
      classifyingSpaceBasepoint (Multiplicative ℤ) := by
    simp
  rw [circleLocalSystemBasepointIso, Iso.trans_hom, eqToIso.hom,
    pullback_obj_map_comp_eqToHom_assoc _ h, classifyingSpaceLocalSystem_map_comp_basepointIso]
  simp [classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace]

/-- **The homology of the circle with local coefficients is the group homology of `ℤ`**: the map
induced by the homotopy equivalence with the classifying space of `ℤ`, followed by
`TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`. -/
def circleTwistedHomologyIsoGroupHomology (n : ℕ) :
    twistedHomology (circleLocalSystem A) n ≅ groupHomology A n :=
  have := circleHomotopyEquivClassifyingSpace.isIso_twistedHomologyMap
    (classifyingSpaceLocalSystem k A) n
  asIso (twistedHomologyMap (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun)
    (classifyingSpaceLocalSystem k A) n) ≪≫ classifyingSpaceTwistedHomologyIsoGroupHomology k A n

/-- **The zeroth homology of the circle with local coefficients** in a representation `A` of `ℤ`
is the module of coinvariants `A / (T - 𝟙) A` of the monodromy
`T = A.ρ (Multiplicative.ofAdd 1)`. -/
def circleTwistedHomologyIso₀ :
    twistedHomology (circleLocalSystem A) 0 ≅
      ModuleCat.of k (A ⧸ LinearMap.range (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) :=
  circleTwistedHomologyIsoGroupHomology A 0 ≪≫
    TauCeti.groupHomology.H0IsoOfForallMemZpowers A Int.mem_zpowers_ofAdd_one

/-- **The first homology of the circle with local coefficients** in a representation `A` of `ℤ`
is the module of invariants `ker (T - 𝟙)` of the monodromy
`T = A.ρ (Multiplicative.ofAdd 1)`. -/
def circleTwistedHomologyIso₁ :
    twistedHomology (circleLocalSystem A) 1 ≅
      ModuleCat.of k (LinearMap.ker (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) :=
  circleTwistedHomologyIsoGroupHomology A 1 ≪≫
    Rep.InfiniteCyclicGroup.groupHomologyIso₁ A Int.mem_zpowers_ofAdd_one
      Int.not_isOfFinOrder_ofAdd_one

/-- **The homology of the circle with local coefficients vanishes in degrees at least `2`.** -/
theorem isZero_circleTwistedHomology_add_two (n : ℕ) :
    Limits.IsZero (twistedHomology (circleLocalSystem A) (n + 2)) :=
  (Rep.InfiniteCyclicGroup.isZero_groupHomology_add_two A Int.mem_zpowers_ofAdd_one
    Int.not_isOfFinOrder_ofAdd_one n).of_iso
    (circleTwistedHomologyIsoGroupHomology A (n + 2))

/-- **The circle with integral coefficients of monodromy `-1` has `H₀ = ℤ / 2`.** -/
def circleTwistedHomologyIntSignRepIso₀ZMod :
    twistedHomology (circleLocalSystem intSignRep) 0 ≅ ModuleCat.of ℤ (ZMod 2) :=
  circleTwistedHomologyIso₀ intSignRep ≪≫
    (Submodule.quotEquivOfEq _ _
        (range_intSignRep_ρ_ofAdd_one_sub_id.trans (by rw [Nat.cast_ofNat])) ≪≫ₗ
      (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv).toModuleIso

/-- **The circle with integral coefficients of monodromy `-1` has `H₁ = 0`**: no nonzero integer
is fixed by `-1`. -/
theorem isZero_circleTwistedHomology_one_intSignRep :
    Limits.IsZero (twistedHomology (circleLocalSystem intSignRep) 1) := by
  refine Limits.IsZero.of_iso ?_ (circleTwistedHomologyIso₁ intSignRep)
  have h : LinearMap.ker (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro (x : ℤ) hx
    rw [intSignRep_ρ_ofAdd_one_sub_id_apply] at hx
    linarith
  rw [h]
  exact ModuleCat.isZero_of_subsingleton _

section Cohomology

variable (N : Type) [AddCommGroup N] [Module k N]

/-- **The cohomology of the circle with local coefficients is the group cohomology of `ℤ`**: with
coefficients in `circleLocalSystem A` and values in a `k`-module `N`, it is the group cohomology of
`ℤ` with coefficients in `Homₖ(A, N)`. This is the inverse of the map induced by the homotopy
equivalence with the classifying space of `ℤ`, followed by
`TauCeti.classifyingSpaceTwistedCohomologyIsoGroupCohomology`. -/
def circleTwistedCohomologyIsoGroupCohomology (n : ℕ) :
    (circleLocalSystem A).twistedCohomology k (ModuleCat.of k N) n ≅
      groupCohomology ((Rep.ihom A).obj (Rep.trivial k (Multiplicative ℤ) N)) n :=
  have := circleHomotopyEquivClassifyingSpace.isIso_twistedCohomologyMap k (ModuleCat.of k N)
    (classifyingSpaceLocalSystem k A) n
  (asIso (twistedCohomologyMap k (ModuleCat.of k N)
    (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun) (classifyingSpaceLocalSystem k A)
      n)).symm ≪≫ classifyingSpaceTwistedCohomologyIsoGroupCohomology k A N n

/-- **The zeroth cohomology of the circle with local coefficients** in a representation `A` of `ℤ`
and values in `N` is the module of the `k`-linear maps `φ : A → N` with `φ ∘ T = φ`, the kernel of
`φ ↦ φ ∘ (T - 𝟙)`, for the monodromy `T = A.ρ (Multiplicative.ofAdd 1)`. -/
def circleTwistedCohomologyIso₀ :
    (circleLocalSystem A).twistedCohomology k (ModuleCat.of k N) 0 ≅
      ModuleCat.of k (LinearMap.ker
        (LinearMap.lcomp k N (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id))) :=
  circleTwistedCohomologyIsoGroupCohomology A N 0 ≪≫
    TauCeti.groupCohomology.H0IsoOfForallMemZpowers _
      (fun x ↦ by rw [Subgroup.zpowers_inv]; exact Int.mem_zpowers_ofAdd_one x) ≪≫
    (LinearEquiv.ofEq _ _
      (congrArg LinearMap.ker (Rep.ihom_obj_trivial_ρ_inv_sub_id A N _))).toModuleIso

/-- **The first cohomology of the circle with local coefficients** in a representation `A` of `ℤ`
and values in `N` is `Homₖ(A, N)` modulo the maps `φ ∘ (T - 𝟙)`, for the monodromy
`T = A.ρ (Multiplicative.ofAdd 1)`. -/
def circleTwistedCohomologyIso₁ :
    (circleLocalSystem A).twistedCohomology k (ModuleCat.of k N) 1 ≅
      ModuleCat.of k ((A →ₗ[k] N) ⧸ LinearMap.range
        (LinearMap.lcomp k N (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id))) :=
  circleTwistedCohomologyIsoGroupCohomology A N 1 ≪≫
    Rep.InfiniteCyclicGroup.groupCohomologyIso₁ _
      (fun x ↦ by rw [Subgroup.zpowers_inv]; exact Int.mem_zpowers_ofAdd_one x)
      (isOfFinOrder_inv_iff.not.2 Int.not_isOfFinOrder_ofAdd_one) ≪≫
    (Submodule.quotEquivOfEq _ _
      (congrArg LinearMap.range (Rep.ihom_obj_trivial_ρ_inv_sub_id A N _))).toModuleIso

/-- **The cohomology of the circle with local coefficients vanishes in degrees at least `2`.** -/
theorem isZero_circleTwistedCohomology_add_two (n : ℕ) :
    Limits.IsZero ((circleLocalSystem A).twistedCohomology k (ModuleCat.of k N) (n + 2)) :=
  (Rep.InfiniteCyclicGroup.isZero_groupCohomology_add_two _ Int.mem_zpowers_ofAdd_one
    Int.not_isOfFinOrder_ofAdd_one n).of_iso (circleTwistedCohomologyIsoGroupCohomology A N (n + 2))

end Cohomology

/-- **The circle with integral coefficients of monodromy `-1` has `H⁰ = 0`** for the cochains with
values in `ℤ`: a map `φ : ℤ → ℤ` with `φ ∘ (-1) = φ` vanishes. -/
theorem isZero_circleTwistedCohomology_zero_intSignRep :
    Limits.IsZero ((circleLocalSystem intSignRep).twistedCohomology ℤ (ModuleCat.of ℤ ℤ) 0) := by
  refine Limits.IsZero.of_iso ?_ (circleTwistedCohomologyIso₀ intSignRep ℤ)
  have h : LinearMap.ker
      (LinearMap.lcomp ℤ ℤ (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    rw [lcomp_intSignRep_ρ_ofAdd_one_sub_id_apply] at hφ
    exact (smul_eq_zero.1 hφ).resolve_left (by norm_num)
  rw [h]
  exact ModuleCat.isZero_of_subsingleton _

/-- **The circle with integral coefficients of monodromy `-1` has `H¹ = ℤ / 2`** for the cochains
with values in `ℤ`: `Hom(ℤ, ℤ) ≅ ℤ`, and precomposition with `T - 𝟙 = -2` is multiplication by
`-2`. -/
def circleTwistedCohomologyIntSignRepIso₁ZMod :
    (circleLocalSystem intSignRep).twistedCohomology ℤ (ModuleCat.of ℤ ℤ) 1 ≅
      ModuleCat.of ℤ (ZMod 2) :=
  circleTwistedCohomologyIso₁ intSignRep ℤ ≪≫
    (Submodule.Quotient.equiv _ _ (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ)
        (map_range_lcomp_intSignRep_ρ_ofAdd_one_sub_id.trans (by rw [Nat.cast_ofNat])) ≪≫ₗ
      (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv).toModuleIso

end TauCeti
