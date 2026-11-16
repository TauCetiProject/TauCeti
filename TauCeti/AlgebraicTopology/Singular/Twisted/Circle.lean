/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Circle
public import TauCeti.AlgebraicTopology.ClassifyingSpace.LocalCoefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.InfiniteCyclic

/-!
# Homology of the circle with local coefficients

A representation `A` of `ℤ` over a commutative ring `k` gives a local coefficient system on the
circle (`TauCeti.circleLocalSystem A`): the system `TauCeti.classifyingSpaceLocalSystem k A` on
Milnor's classifying space of `ℤ`, pulled back along the homotopy equivalence
`TauCeti.circleHomotopyEquivClassifyingSpace`. On the classifying space this system has monodromy
`A.ρ` (`TauCeti.classifyingSpaceLocalSystem_map_comp_basepointIso`), and the map from the circle
induces the identity of `ℤ` on fundamental groups
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`), so the
monodromy of the pulled back system around the circle is `T = A.ρ (Multiplicative.ofAdd 1)`.

A homotopy equivalence induces isomorphisms on homology with local coefficients, and the homology
of the classifying space with these coefficients is group homology, so
`Hₙ(S¹; A) ≅ Hₙ(ℤ, A)` (`TauCeti.circleTwistedHomologyIsoGroupHomology`). The group homology of
the infinite cyclic group (`TauCeti.RepresentationTheory.Homological.GroupHomology.InfiniteCyclic`)
then computes it:

* `H₀(S¹; A) ≅ A / (T - 𝟙) A` (`TauCeti.circleTwistedHomologyIso₀`);
* `H₁(S¹; A) ≅ ker (T - 𝟙)` (`TauCeti.circleTwistedHomologyIso₁`);
* `Hₙ(S¹; A) = 0` for `n ≥ 2` (`TauCeti.isZero_circleTwistedHomology_add_two`).

This is the homology of the cellular complex `A --(T - 𝟙)--> A` of the circle with one vertex and
one edge, whose differential compares the coefficient transported once around the edge with the
coefficient at its start.

For the rank-one integral system of monodromy `-1`, coming from the sign representation
`TauCeti.intSignRep`, the differential is `-2`. Its homology is `H₀ = ℤ / 2`
(`TauCeti.circleTwistedHomologyZeroIntSignIsoZMod`), `H₁ = 0`
(`TauCeti.isZero_circleTwistedHomology_one_intSignRep`) and zero above, although the circle with
constant integral coefficients has `H₀ = H₁ = ℤ`: a cycle running twice around the circle has
coefficient `a + (-1) a = 0`. This local system is the orientation system of the Möbius line
bundle over the circle, the simplest nonorientable line bundle; in Morse–Bott homology such
systems are the coefficients carried by critical circles whose negative normal bundle is a Möbius
line.

## Main definitions

* `TauCeti.circleLocalSystem`: the local system on the circle of a representation of `ℤ`.
* `TauCeti.circleTwistedHomologyIsoGroupHomology`: `Hₙ(S¹; A) ≅ Hₙ(ℤ, A)`.
* `TauCeti.circleTwistedHomologyIso₀`, `TauCeti.circleTwistedHomologyIso₁`: the homology in
  degrees `0` and `1`.
* `TauCeti.intSignRep`: the integral sign representation of `ℤ`.
* `TauCeti.circleTwistedHomologyZeroIntSignIsoZMod`: `H₀(S¹; ℤ⁻) ≅ ℤ / 2`.

## Main results

* `TauCeti.isZero_circleTwistedHomology_add_two`: `Hₙ(S¹; A) = 0` for `n ≥ 2`.
* `TauCeti.isZero_circleTwistedHomology_one_intSignRep`: `H₁(S¹; ℤ⁻) = 0`.

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
circle is `A.ρ (Multiplicative.ofAdd 1)`. -/
abbrev circleLocalSystem : LocalCoefficientSystem k (TopCat.of Circle) :=
  (pullback (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun).hom).obj
    (classifyingSpaceLocalSystem k A)

/-- **The homology of the circle with local coefficients is the group homology of `ℤ`**: the map
induced by the homotopy equivalence with the classifying space of `ℤ`, followed by
`TauCeti.classifyingSpaceTwistedHomologyIsoGroupHomology`. -/
def circleTwistedHomologyIsoGroupHomology (n : ℕ) :
    twistedHomology (circleLocalSystem A) n ≅ groupHomology A n :=
  have := circleHomotopyEquivClassifyingSpace.isIso_twistedHomologyMap
    (classifyingSpaceLocalSystem k A) n
  asIso (twistedHomologyMap (TopCat.ofHom circleHomotopyEquivClassifyingSpace.toFun)
    (classifyingSpaceLocalSystem k A) n) ≪≫ classifyingSpaceTwistedHomologyIsoGroupHomology k A n

/-- `Multiplicative.ofAdd 1` generates `Multiplicative ℤ`, the multiplicative form of
`Int.zmultiples_one`. -/
theorem _root_.Int.mem_zpowers_ofAdd_one (x : Multiplicative ℤ) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) :=
  Subgroup.mem_zpowers_iff.2 ⟨x.toAdd, by rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]⟩

/-- **The zeroth homology of the circle with local coefficients** in a representation `A` of `ℤ`
is the module of coinvariants `A / (T - 𝟙) A` of the monodromy `T = ρ(1)`. -/
def circleTwistedHomologyIso₀ :
    twistedHomology (circleLocalSystem A) 0 ≅
      ModuleCat.of k (A ⧸ LinearMap.range (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) :=
  circleTwistedHomologyIsoGroupHomology A 0 ≪≫
    Rep.InfiniteCyclicGroup.groupHomologyIso₀ A Int.mem_zpowers_ofAdd_one

/-- **The first homology of the circle with local coefficients** in a representation `A` of `ℤ`
is the module of invariants `ker (T - 𝟙)` of the monodromy `T = ρ(1)`. -/
def circleTwistedHomologyIso₁ :
    twistedHomology (circleLocalSystem A) 1 ≅
      ModuleCat.of k (LinearMap.ker (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) :=
  circleTwistedHomologyIsoGroupHomology A 1 ≪≫
    Rep.InfiniteCyclicGroup.groupHomologyIso₁ A Int.mem_zpowers_ofAdd_one
      (isOfFinOrder_ofAdd_iff.not.2 (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero))

/-- **The homology of the circle with local coefficients vanishes in degrees at least `2`.** -/
theorem isZero_circleTwistedHomology_add_two (n : ℕ) :
    Limits.IsZero (twistedHomology (circleLocalSystem A) (n + 2)) :=
  (Rep.InfiniteCyclicGroup.isZero_groupHomology_add_two A Int.mem_zpowers_ofAdd_one
    (isOfFinOrder_ofAdd_iff.not.2 (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)) n).of_iso
    (circleTwistedHomologyIsoGroupHomology A (n + 2))

/-- The integral sign representation of `ℤ`, in which `n` acts on `ℤ` by `(-1) ^ n`. Its local
system on the circle is the rank-one integral system of monodromy `-1`. -/
abbrev intSignRep : Rep ℤ (Multiplicative ℤ) :=
  Rep.of ((Units.coeHom (Module.End ℤ ℤ)).comp (zpowersHom (Module.End ℤ ℤ)ˣ (-1)))

/-- The generator of `ℤ` acts by `-1` in the sign representation. -/
theorem intSignRep_ρ_ofAdd_one : intSignRep.ρ (Multiplicative.ofAdd 1) = -1 := by
  simp [intSignRep]

/-- In the sign representation, `T - 𝟙 = -2` has range `2ℤ`. -/
theorem range_intSignRep_ρ_ofAdd_one_sub_id :
    LinearMap.range (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id) =
      Ideal.span {((2 : ℕ) : ℤ)} := by
  ext x
  rw [intSignRep_ρ_ofAdd_one]
  simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearMap.neg_apply, one_apply_eq_self,
    LinearMap.id_apply, Nat.cast_ofNat, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨-y, by ring⟩

/-- **The circle with integral coefficients of monodromy `-1` has `H₀ = ℤ / 2`.** -/
def circleTwistedHomologyZeroIntSignIsoZMod :
    twistedHomology (circleLocalSystem intSignRep) 0 ≅ ModuleCat.of ℤ (ZMod 2) :=
  circleTwistedHomologyIso₀ intSignRep ≪≫
    (Submodule.quotEquivOfEq _ _ range_intSignRep_ρ_ofAdd_one_sub_id ≪≫ₗ
      (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv).toModuleIso

/-- **The circle with integral coefficients of monodromy `-1` has `H₁ = 0`**: no nonzero integer
is fixed by `-1`. -/
theorem isZero_circleTwistedHomology_one_intSignRep :
    Limits.IsZero (twistedHomology (circleLocalSystem intSignRep) 1) := by
  refine Limits.IsZero.of_iso ?_ (circleTwistedHomologyIso₁ intSignRep)
  have h : LinearMap.ker (intSignRep.ρ (Multiplicative.ofAdd 1) - LinearMap.id) = ⊥ := by
    rw [intSignRep_ρ_ofAdd_one, LinearMap.ker_eq_bot']
    intro (x : ℤ) hx
    rw [LinearMap.sub_apply, LinearMap.neg_apply, one_apply_eq_self, LinearMap.id_apply] at hx
    linarith
  rw [h]
  exact ModuleCat.isZero_of_subsingleton _

end TauCeti
