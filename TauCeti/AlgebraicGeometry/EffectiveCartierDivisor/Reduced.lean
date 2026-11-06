/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.DiscreteValuationRing.Length

/-!
# Reduced principal divisors on locally factorial schemes

The zero scheme of a nonzero function on a locally Noetherian integral scheme with factorial
local rings is reduced exactly when its orders at all codimension-one points are at most one.
In particular, reducedness is detected at the generic points of the divisor's components:
factoriality excludes embedded nilpotents at their intersections. This is the criterion that
turns multiplicity-one components of a special fibre into a reduced scheme-theoretic fibre.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.11, locally factorial schemes.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, multiplicities of fibres.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

local instance nonemptyTopForSquarefreeGerm : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- If the orders of a nonzero global function at all codimension-one points are at most one,
its germs in factorial local rings are squarefree. -/
theorem squarefree_germ_of_forall_ord_le_one {f : Γ(X, ⊤)} (hf : f ≠ 0)
    (hord : ∀ η : CodimensionOnePoint X, X.ord (X.germToFunctionField ⊤ f) η ≤ 1)
    (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    Squarefree (X.presheaf.germ ⊤ x trivial f) := by
  have hb : X.presheaf.germ ⊤ x trivial f ≠ 0 := fun h ↦
    hf (germ_injective_of_isIntegral X x trivial (h.trans (map_zero _).symm))
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hb]
  intro p hp ⟨a, ha⟩
  obtain ⟨η, hη, hηx, hprime⟩ :=
    TauCeti.AlgebraicGeometry.Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq_span_singleton
      (irreducible_iff_prime.mp hp)
  have hp0 := hp.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hb (by simpa only [mul_zero] using ha)
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hpK : algebraMap (X.presheaf.stalk x) X.functionField p ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hp0
  have haK : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ha0
  have hbound := hord ⟨η, hη⟩
  have hnonneg := TauCeti.AlgebraicGeometry.Scheme.ord_algebraMap_stalk_nonneg hη hηx ha0
  rw [← X.algebraMap_germ_eq_germToFunctionField (x := x) trivial f, ha, map_mul,
    map_mul, X.ord_mul (mul_ne_zero hpK hpK) haK, X.ord_mul hpK hpK,
    TauCeti.AlgebraicGeometry.Scheme.ord_algebraMap_stalk_eq_one hη hηx hprime hp0] at hbound
  -- Normalize the bundled codimension-one point before comparing the integer orders.
  dsimp only at hbound
  omega

end TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance nonemptyTopForReducedDivisor : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The zero scheme of a nonzero global function on a locally factorial, locally Noetherian
integral scheme is reduced exactly when every codimension-one order is at most one. -/
theorem isReduced_subscheme_ofIdealTop_span_singleton_iff_ord_le_one
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] {f : Γ(X, ⊤)} (hf : f ≠ 0) :
    IsReduced (ofIdealTop (Ideal.span {f})).subscheme ↔
      ∀ η : CodimensionOnePoint X, X.ord (X.germToFunctionField ⊤ f) η ≤ 1 := by
  rw [isReduced_subscheme_ofIdealTop_span_singleton_iff]
  constructor
  · intro h η
    have : IsDiscreteValuationRing (X.presheaf.stalk (η : X)) :=
      IsDiscreteValuationRing.of_ringKrullDim_eq_one (by
        rw [ringKrullDim_stalk_eq_coheight, η.property]
        norm_cast)
    have hb : X.presheaf.germ ⊤ (η : X) trivial f ≠ 0 := fun he ↦
      hf (germ_injective_of_isIntegral X η trivial (he.trans (map_zero _).symm))
    have hle := (TauCeti.Ring.squarefree_iff_ord_le_one hb).mp ((h η).squarefree hb)
    have hnt := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hb)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnt
    rw [← X.algebraMap_germ_eq_germToFunctionField (x := (η : X)) trivial f,
      TauCeti.AlgebraicGeometry.Scheme.ord_algebraMap_stalk η.property hb, ← hn,
      ENat.toNat_natCast]
    rw [← hn] at hle
    exact_mod_cast hle
  · exact fun h x ↦
      (TauCeti.AlgebraicGeometry.Scheme.squarefree_germ_of_forall_ord_le_one hf h x).isRadical

end AlgebraicGeometry.Scheme.IdealSheafData
