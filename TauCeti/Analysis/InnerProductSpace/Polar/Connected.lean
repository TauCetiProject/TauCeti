/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.UnitaryLog
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Norm-path-connectedness of `GL(H)` via polar decomposition and Borel unitary logarithms

Every invertible bounded linear operator `T` on a complex Hilbert space `H` factors through its
right polar decomposition `T = U |T|` (`ContinuousLinearMap.polarFactor_comp_modulus`), where:

* `U = T.polarFactor` is unitary (`ContinuousLinearMap.polarFactor_mem_unitary`) and agrees with
  the abstract C⋆-algebraic polar unitary `Units.polarUnitary`
  (`Units.coe_polarUnitary_eq_polarFactor`), and
* `|T| = T.modulus` is strictly positive
  (`ContinuousLinearMap.isStrictlyPositive_modulus_of_isInvertible`).

Combining two explicit norm-continuous paths on `[0, 1]`:

1. the single-exponential unitary path
   `t ↦ selfAdjoint.expUnitary (t • Unitary.borelArgSelfAdjoint U)` from `1` to `U`
   (`Unitary.borelPathFromOne`), and
2. the affine straight-line path `t ↦ AffineMap.lineMap 1 |T| t = (1 - t) • 1 + t • |T|` from `1`
   to `|T|`, which stays strictly positive — hence invertible — at every `t ∈ [0, 1]`
   (`ContinuousLinearMap.isStrictlyPositive_lineMap_one_modulus`),

produces an explicit norm-continuous path

`t ↦ expUnitary (t • borelArgSelfAdjoint U) ∘L AffineMap.lineMap 1 |T| t`

joining the identity operator to `T` inside `GL(H)` (`Units.polarLinearPathFromOne`,
`ContinuousLinearMap.IsInvertible.polarLinearPathFromId`). Consequently `(H →L[ℂ] H)ˣ`, as well as
the subsets `{T : H →L[ℂ] H | IsUnit T}` and `{T : H →L[ℂ] H | T.IsInvertible}` equipped with the
operator-norm subspace topology, are globally path-connected
(`ContinuousLinearMap.instPathConnectedSpaceUnits`,
`ContinuousLinearMap.isPathConnected_setOf_isUnit`,
`ContinuousLinearMap.isPathConnected_setOf_isInvertible`).

Over `ℝ`, by contrast, `GL(ℝ)` already has two connected components separated by the sign of the
determinant; complex scalars enter through the Borel unitary logarithm
`Unitary.borelArgSelfAdjoint`.

## References

* C. R. Putnam and A. Wintner, *The orthogonal invariants of two subspaces of a Hilbert space*,
  Amer. J. Math. 74 (1952), 578–584.
* N. H. Kuiper, *The homotopy type of the unitary group of Hilbert space*, Topology 3 (1965),
  19–30 (for contractibility, whereas path-connectedness uses only the spectral theorem and polar
  decomposition).
* D. S. Freed, *The Atiyah–Singer index theorem*, Bull. Amer. Math. Soc. (N.S.) 58 (2021),
  517–566, §3.
-/

public section

noncomputable section

open Set

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On a Hilbert space endomorphism algebra, the C⋆-algebraic polar unitary `Units.polarUnitary u`
agrees with the Hilbert-space polar factor `(u : E →L[𝕜] E).polarFactor`. -/
@[simp]
theorem Units.coe_polarUnitary_eq_polarFactor [Algebra ℝ (E →L[𝕜] E)]
    [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] (u : (E →L[𝕜] E)ˣ) :
    (u.polarUnitary : E →L[𝕜] E) = (u : E →L[𝕜] E).polarFactor := by
  let v : unitary (E →L[𝕜] E) :=
    ⟨(u : E →L[𝕜] E).polarFactor, (u : E →L[𝕜] E).polarFactor_mem_unitary u.isUnit⟩
  have hv : u.polarUnitary = v :=
    u.polarUnitary_eq_of_mul_eq' (u : E →L[𝕜] E).modulus_nonneg
      (u : E →L[𝕜] E).polarFactor_comp_modulus
  exact congrArg Subtype.val hv

end RCLike

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [StarModule ℝ A]

/-- Strictly positive elements in a star-ordered unital C⋆-algebra form a convex set. -/
theorem TauCeti.convex_setOf_isStrictlyPositive : Convex ℝ {a : A | IsStrictlyPositive a} :=
  convex_iff_forall_pos.mpr fun _ ha _ hb _ _ hc hd _ ↦
    (ha.smul hc).add_nonneg (smul_nonneg hd.le hb.nonneg)

/-- Along the closed unit interval `[0, 1]`, the straight-line segment `AffineMap.lineMap a b t`
between two strictly positive elements of a star-ordered unital C⋆-algebra remains strictly
positive. -/
theorem IsStrictlyPositive.lineMap {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) {t : ℝ} (ht : t ∈ Icc 0 1) :
    IsStrictlyPositive (AffineMap.lineMap a b t) := by
  rw [AffineMap.lineMap_apply_module]
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · simpa using ha
  · exact IsStrictlyPositive.nonneg_add (smul_nonneg (sub_nonneg.mpr ht.2) ha.nonneg)
      (hb.smul ht_pos)

end CStarAlgebra

section ComplexHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- For an invertible operator `T : H →L[ℂ] H` and `t ∈ [0, 1]`, the convex combination
`(1 - t) • 1 + t • |T| = AffineMap.lineMap 1 T.modulus t` is strictly positive, hence invertible.
-/
theorem isStrictlyPositive_lineMap_one_modulus {T : H →L[ℂ] H} (hT : IsUnit T) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    IsStrictlyPositive (AffineMap.lineMap 1 T.modulus t) :=
  isStrictlyPositive_one.lineMap
    (isStrictlyPositive_modulus_of_isInvertible (isInvertible_iff_isUnit.mpr hT)) ht

/-- Every point on the straight-line segment from `1` to `T.modulus` (`t ∈ [0, 1]`) is a unit when
`T` is a unit. -/
theorem isUnit_lineMap_one_modulus {T : H →L[ℂ] H} (hT : IsUnit T) {t : ℝ} (ht : t ∈ Icc 0 1) :
    IsUnit (AffineMap.lineMap 1 T.modulus t) :=
  (isStrictlyPositive_lineMap_one_modulus hT ht).isUnit

end ContinuousLinearMap

namespace Units

/-- **Explicit polar-linear path in `(H →L[ℂ] H)ˣ`.** Every invertible bounded operator `u` on a
complex Hilbert space is joined to `1` by combining the single-exponential Borel path from `1` to
`u.polarUnitary` with the straight-line path `AffineMap.lineMap 1 |u|` in the strictly positive
cone. -/
def polarLinearPathFromOne (u : (H →L[ℂ] H)ˣ) : Path 1 u where
  toFun t :=
    Unitary.toUnits (Unitary.borelPathFromOne (H := H) u.polarUnitary t) *
      (ContinuousLinearMap.isUnit_lineMap_one_modulus u.isUnit t.2).unit
  continuous_toFun := by
    rw [Units.isOpenEmbedding_val.isInducing.continuous_iff]
    have hcont : Continuous fun t : unitInterval ↦
        (Unitary.borelPathFromOne (H := H) u.polarUnitary t : H →L[ℂ] H) *
          AffineMap.lineMap 1 (u : H →L[ℂ] H).modulus (t : ℝ) := by
      fun_prop
    refine hcont.congr fun t ↦ ?_
    simp
  source' := by
    ext1
    simp
  target' := by
    ext1
    simp [coe_polarUnitary_eq_polarFactor, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.polarFactor_comp_modulus]

/-- At `t ∈ [0, 1]`, `u.polarLinearPathFromOne t` evaluates in `H →L[ℂ] H` to
`expUnitary (t • borelArgSelfAdjoint u.polarUnitary) ∘L AffineMap.lineMap 1 |u| t`. -/
@[simp]
theorem val_polarLinearPathFromOne_apply (u : (H →L[ℂ] H)ˣ) (t : unitInterval) :
    ((u.polarLinearPathFromOne t : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
      (selfAdjoint.expUnitary
        ((t : ℝ) • Unitary.borelArgSelfAdjoint (H := H) u.polarUnitary) : H →L[ℂ] H) ∘L
        AffineMap.lineMap 1 (u : H →L[ℂ] H).modulus (t : ℝ) := by
  simp [polarLinearPathFromOne, ContinuousLinearMap.mul_def]

/-- Every unit in `(H →L[ℂ] H)ˣ` is joined by a norm-continuous path to `1`. -/
theorem joined_one_clm (u : (H →L[ℂ] H)ˣ) : Joined (1 : (H →L[ℂ] H)ˣ) u :=
  ⟨u.polarLinearPathFromOne⟩

end Units

namespace ContinuousLinearMap

/-- **Global norm-path-connectedness of `GL(H)`.** The group of units `(H →L[ℂ] H)ˣ` of a complex
Hilbert space is path-connected. -/
instance instPathConnectedSpaceUnits : PathConnectedSpace (H →L[ℂ] H)ˣ :=
  PathConnectedSpace.mk ⟨1⟩ fun u v ↦ (u.joined_one_clm).symm.trans v.joined_one_clm

/-- The invertible bounded operators `{T : H →L[ℂ] H | IsUnit T}` form a path-connected subset of
`H →L[ℂ] H` in the operator norm. -/
theorem isPathConnected_setOf_isUnit : IsPathConnected {T : H →L[ℂ] H | IsUnit T} := by
  have hrng : range (Units.val : (H →L[ℂ] H)ˣ → H →L[ℂ] H) = {T : H →L[ℂ] H | IsUnit T} := by
    ext T
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.isUnit, fun hT ↦ ⟨hT.unit, hT.unit_spec⟩⟩
  rw [← hrng]
  exact isPathConnected_range Units.continuous_val

/-- The invertible bounded operators `{T : H →L[ℂ] H | T.IsInvertible}` form a path-connected
subset of `H →L[ℂ] H` in the operator norm. -/
theorem isPathConnected_setOf_isInvertible :
    IsPathConnected {T : H →L[ℂ] H | T.IsInvertible} := by
  convert isPathConnected_setOf_isUnit (H := H) using 1
  ext T
  exact isInvertible_iff_isUnit

/-- The subtype `{T : H →L[ℂ] H // T.IsInvertible}` of invertible bounded operators on a complex
Hilbert space is path-connected in the operator-norm subspace topology. -/
instance instPathConnectedSpaceSubtypeIsInvertible :
    PathConnectedSpace {T : H →L[ℂ] H // T.IsInvertible} :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_setOf_isInvertible

/-- Explicit operator-norm continuous path in `{T : H →L[ℂ] H // T.IsInvertible}` from the identity
operator to `⟨T, hT⟩` via the polar-linear path `Units.polarLinearPathFromOne`. -/
def IsInvertible.polarLinearPathFromId {T : H →L[ℂ] H} (hT : T.IsInvertible) :
    Path
      (⟨ContinuousLinearMap.id ℂ H, ⟨ContinuousLinearEquiv.refl ℂ H, rfl⟩⟩ :
        {S : H →L[ℂ] H // S.IsInvertible})
      ⟨T, hT⟩ where
  toFun t :=
    ⟨(((isInvertible_iff_isUnit.mp hT).unit.polarLinearPathFromOne t : (H →L[ℂ] H)ˣ) : H →L[ℂ] H),
      isInvertible_iff_isUnit.mpr
        ((isInvertible_iff_isUnit.mp hT).unit.polarLinearPathFromOne t).isUnit⟩
  continuous_toFun := (Units.continuous_val.comp (Path.continuous _)).subtype_mk _
  source' := by
    ext x
    simp
  target' := by
    ext1
    simp

/-- Evaluating `IsInvertible.polarLinearPathFromId` gives the polar-linear operator formula
`expUnitary (t • borelArgSelfAdjoint U) ∘L AffineMap.lineMap 1 |T| t`. -/
@[simp]
theorem IsInvertible.coe_polarLinearPathFromId_apply {T : H →L[ℂ] H} (hT : T.IsInvertible)
    (t : unitInterval) :
    ((hT.polarLinearPathFromId t : {S : H →L[ℂ] H // S.IsInvertible}) : H →L[ℂ] H) =
      (selfAdjoint.expUnitary
          ((t : ℝ) • Unitary.borelArgSelfAdjoint (H := H)
            ⟨T.polarFactor, T.polarFactor_mem_unitary (isInvertible_iff_isUnit.mp hT)⟩) :
        H →L[ℂ] H) ∘L AffineMap.lineMap 1 T.modulus (t : ℝ) := by
  let u : (H →L[ℂ] H)ˣ := (isInvertible_iff_isUnit.mp hT).unit
  have hu : (u : H →L[ℂ] H) = T := (isInvertible_iff_isUnit.mp hT).unit_spec
  have hpol : u.polarUnitary =
      ⟨T.polarFactor, T.polarFactor_mem_unitary (isInvertible_iff_isUnit.mp hT)⟩ := by
    ext1
    simp [hu]
  have hval : ((hT.polarLinearPathFromId t : {S : H →L[ℂ] H // S.IsInvertible}) : H →L[ℂ] H) =
      ((u.polarLinearPathFromOne t : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := rfl
  rw [hval, Units.val_polarLinearPathFromOne_apply, hpol, hu]

end ContinuousLinearMap

end ComplexHilbert
