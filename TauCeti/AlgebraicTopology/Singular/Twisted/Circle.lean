/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.Algebra.Group.ZMultiples
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Circle
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Monodromy
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.InfiniteCyclic
public import TauCeti.RepresentationTheory.LinearCharacter.Sign

/-!
# Homology of the circle with local coefficients

A representation `A` of `ℤ = π₁(S¹)` over a commutative ring `k` gives a local coefficient system
on the circle, `TauCeti.circleLocalSystem k A`: the pullback, along the map
`TauCeti.circleToClassifyingSpace` which wraps the circle once around the generator, of the
local system on the classifying space of `ℤ` associated to `A`. Its fibre at `1` is `A`
(`TauCeti.circleLocalSystemBasepointIso`), and transport around a loop of degree `n` acts by
`ρ(n)` (`TauCeti.circleLocalSystem_map_comp_basepointIso`). So its monodromy around the generator
is `T = ρ(1)`.

The circle is homotopy equivalent to the classifying space of `ℤ`, so its homology with these
coefficients is the group homology of `ℤ` with coefficients in `A`
(`TauCeti.circleTwistedHomologyIsoGroupHomology`). Computed from the length-one resolution of an
infinite cyclic group, this is the homology of the cellular complex of the circle with one vertex
and one edge, whose differential is `T - 1`:

* `H₀(S¹; A) ≅ A / (T - 1) A` (`TauCeti.circleTwistedHomologyZeroIso`);
* `H₁(S¹; A) ≅ A^ℤ = ker (T - 1)` (`TauCeti.circleTwistedHomologyOneIso`);
* `Hₙ(S¹; A) = 0` for `n ≥ 2` (`TauCeti.isZero_circleTwistedHomology_add_two`).

For the rank-one integral system with monodromy `-1`, the coefficient system
`TauCeti.circleLocalSystem ℤ TauCeti.intSignRep` of the sign representation `n ↦ (-1)ⁿ`
(from `TauCeti.RepresentationTheory.LinearCharacter.Sign`), the
differential `T - 1` is multiplication by `-2`. Hence `H₀(S¹; ℤ⁻) ≅ ℤ/2`
(`TauCeti.circleTwistedHomologyIntSignRepZeroIso`) and `H₁(S¹; ℤ⁻) = 0`
(`TauCeti.isZero_circleTwistedHomology_intSignRep_one`), whereas with constant coefficients both
groups are `ℤ`. This is the orientation-line computation for a negative bundle with monodromy `-1`
along a circle of critical points of a Morse–Bott function, such as the Möbius line over the
maximum circle of the height function on the Klein bottle.

## Main definitions

* `TauCeti.circleLocalSystem`: the local system on the circle associated to a representation of
  `ℤ`.
* `TauCeti.circleLocalSystemBasepointIso`: its fibre at `1` is the representation.
* `TauCeti.circleTwistedHomologyIsoGroupHomology`: `Hₙ(S¹; A) ≅ Hₙ(ℤ, A)`.
* `TauCeti.circleTwistedHomologyZeroIso`, `TauCeti.circleTwistedHomologyOneIso`: the homology in
  degrees `0` and `1`.
* `TauCeti.circleTwistedHomologyIntSignRepZeroIso`: `H₀(S¹; ℤ⁻) ≅ ℤ/2`.

## Main results

* `TauCeti.circleLocalSystem_map_comp_basepointIso`: the monodromy is the action of `ℤ` on `A`.
* `TauCeti.isZero_circleTwistedHomology_add_two`: no homology above degree one.
* `TauCeti.isZero_circleTwistedHomology_intSignRep_one`: `H₁(S¹; ℤ⁻) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (homology with
  local coefficients, and the cellular computation for a circle).
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter III, Section 1 (the homology of an infinite cyclic group).
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

namespace TauCeti

variable {k : Type} [CommRing k] (A : Rep k (Multiplicative ℤ))

variable (k) in
/-- The local coefficient system on the circle associated to a representation `A` of
`ℤ = π₁(S¹)`: the pullback along `circleToClassifyingSpace` of the local system on the classifying
space of `ℤ` associated to `A`. Its monodromy around a loop of degree `n` is `A.ρ n`
(`circleLocalSystem_map_comp_basepointIso`). -/
abbrev circleLocalSystem : LocalCoefficientSystem k (TopCat.of Circle) :=
  (pullback circleToClassifyingSpace).obj (classifyingSpaceLocalSystem k A)

/-- `circleToClassifyingSpace` sends the base point `1` of the circle to the base point of the
classifying space, as points of the fundamental groupoid. -/
private lemma fundamentalGroupoidMap_circleToClassifyingSpace_obj_one :
    (FundamentalGroupoid.map circleToClassifyingSpace).obj (FundamentalGroupoid.mk 1) =
      FundamentalGroupoid.mk (classifyingSpaceBasepoint (Multiplicative ℤ)) :=
  congrArg FundamentalGroupoid.mk circleToClassifyingSpace_one

/-- The image of a loop at `1` under `circleToClassifyingSpace`, as a loop at the base point, is
its image in the fundamental groupoid conjugated by the identification of the base points. -/
private lemma asHom_mapOfEq_circleToClassifyingSpace (γ : FundamentalGroup Circle 1) :
    (FundamentalGroup.mapOfEq circleToClassifyingSpace circleToClassifyingSpace_one γ).asHom =
      eqToHom fundamentalGroupoidMap_circleToClassifyingSpace_obj_one.symm ≫
        (FundamentalGroupoid.map circleToClassifyingSpace).map γ.asHom ≫
          eqToHom fundamentalGroupoidMap_circleToClassifyingSpace_obj_one :=
  (rfl)

/-- The fibre of `circleLocalSystem k A` at `1` is `A`, through the fibre of the classifying-space
system at its base point. -/
def circleLocalSystemBasepointIso :
    (circleLocalSystem k A).obj (FundamentalGroupoid.mk 1) ≅ ModuleCat.of k A :=
  (classifyingSpaceLocalSystem k A).mapIso
      (eqToIso fundamentalGroupoidMap_circleToClassifyingSpace_obj_one) ≪≫
    classifyingSpaceLocalSystemBasepointIso k A

/-- **The monodromy of `circleLocalSystem k A` is the action of `ℤ` on `A`**: under the
identification of the fibre at `1` with `A`, transport around a loop `γ` is `A.ρ` of the degree
of `γ`. -/
@[reassoc]
theorem circleLocalSystem_map_comp_basepointIso (γ : FundamentalGroup Circle 1) :
    (circleLocalSystem k A).map γ.asHom ≫ (circleLocalSystemBasepointIso A).hom =
      (circleLocalSystemBasepointIso A).hom ≫
        ModuleCat.ofHom (A.ρ (Circle.fundamentalGroupMulEquiv 1 γ)) := by
  have key := classifyingSpaceLocalSystem_map_comp_basepointIso k A
    (FundamentalGroup.mapOfEq circleToClassifyingSpace circleToClassifyingSpace_one γ)
  rw [classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace,
    asHom_mapOfEq_circleToClassifyingSpace, Functor.map_comp, Functor.map_comp] at key
  -- Precomposing with the transport between the base points cancels the conjugation in `key`.
  have h := congrArg ((classifyingSpaceLocalSystem k A).map
    (eqToHom fundamentalGroupoidMap_circleToClassifyingSpace_obj_one) ≫ ·) key
  simp only [← Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
    Category.id_comp] at h
  simp only [Functor.map_comp, Category.assoc] at h
  -- `circleLocalSystem` is the pullback, whose transport and fibres are those of the
  -- classifying-space system along `circleToClassifyingSpace`, so `h` is the goal.
  exact h

instance isIso_twistedHomologyMap_circleToClassifyingSpace (n : ℕ) :
    IsIso (twistedHomologyMap (TopCat.ofHom circleToClassifyingSpace)
      (classifyingSpaceLocalSystem k A) n) := by
  have h := circleHomotopyEquivClassifyingSpace.isIso_twistedHomologyMap
    (classifyingSpaceLocalSystem k A) n
  rwa [circleHomotopyEquivClassifyingSpace_toFun] at h

/-- **The homology of the circle with local coefficients is the group homology of `ℤ`**:
`Hₙ(S¹; A) ≅ Hₙ(ℤ, A)`, through the map induced by `circleToClassifyingSpace`, a homotopy
equivalence. -/
def circleTwistedHomologyIsoGroupHomology (n : ℕ) :
    twistedHomology (circleLocalSystem k A) n ≅ groupHomology A n :=
  asIso (twistedHomologyMap (TopCat.ofHom circleToClassifyingSpace)
    (classifyingSpaceLocalSystem k A) n) ≪≫ classifyingSpaceTwistedHomologyIsoGroupHomology k A n

/-- **The circle has no homology above degree one**, with any local coefficients. -/
theorem isZero_circleTwistedHomology_add_two (n : ℕ) :
    Limits.IsZero (twistedHomology (circleLocalSystem k A) (n + 2)) :=
  (Rep.InfiniteCyclicGroup.isZero_groupHomology_add_two A
    Multiplicative.mem_zpowers_ofAdd_one_int n).of_iso
      (circleTwistedHomologyIsoGroupHomology A (n + 2))

/-- **The first homology of the circle with local coefficients** is the module of invariants of
the monodromy, `H₁(S¹; A) ≅ A^ℤ`. -/
def circleTwistedHomologyOneIso :
    twistedHomology (circleLocalSystem k A) 1 ≅ ModuleCat.of k A.ρ.invariants :=
  circleTwistedHomologyIsoGroupHomology A 1 ≪≫
    Rep.InfiniteCyclicGroup.groupHomologyOneIso A Multiplicative.mem_zpowers_ofAdd_one_int

/-- **The zeroth homology of the circle with local coefficients** is the module of coinvariants of
the monodromy `T`, `H₀(S¹; A) ≅ A / (T - 1) A`. -/
def circleTwistedHomologyZeroIso :
    twistedHomology (circleLocalSystem k A) 0 ≅
      ModuleCat.of k (A ⧸ LinearMap.range (A.ρ (Multiplicative.ofAdd 1) - LinearMap.id)) :=
  circleTwistedHomologyIsoGroupHomology A 0 ≪≫
    Rep.InfiniteCyclicGroup.groupHomologyZeroIso A Multiplicative.mem_zpowers_ofAdd_one_int

/-- **The circle has no first homology with coefficients in the sign system**: `H₁(S¹; ℤ⁻) = 0`,
since no nonzero integer is fixed by `-1`. -/
theorem isZero_circleTwistedHomology_intSignRep_one :
    Limits.IsZero (twistedHomology (circleLocalSystem ℤ intSignRep) 1) := by
  refine Limits.IsZero.of_iso ?_ (circleTwistedHomologyOneIso intSignRep)
  rw [ModuleCat.isZero_iff_subsingleton, invariants_intSignRep]
  infer_instance

/-- **The zeroth homology of the circle with coefficients in the sign system is `ℤ/2`**:
`H₀(S¹; ℤ⁻) ≅ ℤ / 2ℤ`, the cokernel of the cellular differential `T - 1 = -2`. -/
def circleTwistedHomologyIntSignRepZeroIso :
    twistedHomology (circleLocalSystem ℤ intSignRep) 0 ≅ ModuleCat.of ℤ (ZMod 2) :=
  circleTwistedHomologyZeroIso intSignRep ≪≫
    ((Submodule.quotEquivOfEq _ _ range_intSignRep_ρ_ofAdd_one_sub_id).trans
      (Int.quotientSpanNatEquivZMod 2).toIntLinearEquiv).toModuleIso

end TauCeti
