/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialUnitaryFrobenius
public import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection

/-!
# Unitary transvections in the finite special unitary groups

Let `d` be a valid Lie-type index with characteristic `p` and field order `q = p ^ e`, let `K` be
the field with `q²` elements and `σ : x ↦ x ^ q` its involution, and let `Q` be the signed
reversal matrix `TauCeti.typeAGraphConjugator r K`. By
`TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`, the fixed subgroup
of the graph-twisted Frobenius `TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius` is the
special unitary group `SU_{r+1}(q)` of the `σ`-sesquilinear form `B(x, y) = σ(x)ᵀ Q y`, which is
`TauCeti.ValidLieTypeIndex.unitaryForm`, defined with its basic properties in
`CFSG/SpecialUnitaryFrobenius.lean`. It satisfies `B(y, x) = (-1) ^ r σ(B(x, y))`
(`TauCeti.ValidLieTypeIndex.unitaryForm_swap`).

For an isotropic vector `v`, `B(v, v) = 0`, and a scalar `a` with `a + (-1) ^ r σ(a) = 0`, the
unitary transvection `τ_{v,a} : x ↦ x + a B(v, x) v` of `Matrix.unitaryTransvection` lies in
`SU_{r+1}(q)`. The admissible scalars form the additive subgroup
`TauCeti.ValidLieTypeIndex.unitaryTransvectionScalars`, and `a ↦ τ_{v,a}` is a homomorphism
`TauCeti.ValidLieTypeIndex.unitaryTransvectionHom` from it, so the transvections along `v` form an
abelian subgroup of `SU_{r+1}(q)`, its range. An element `g` of `SU_{r+1}(q)` conjugates
`τ_{v,a}` to `τ_{g v,a}`, and rescaling `v` by a nonzero scalar does not change the subgroup. So
these subgroups are attached to the isotropic points of projective space and are permuted by
`SU_{r+1}(q)` like those points. This is the commutativity and conjugation part of an Iwasawa
structure for the action of `SU_{r+1}(q)` on its isotropic points, the action through which the
simplicity of the projective special unitary groups `PSU_{r+1}(q)`, the groups `²A_r(q)` of the
classification list, is proved by Iwasawa's criterion `MulAction.IwasawaStructure.isSimpleGroup`.
Generation of `SU_{r+1}(q)` by these subgroups is not proved here.

## Main definitions

* `TauCeti.ValidLieTypeIndex.unitaryTransvectionScalars`: the scalars `a` with
  `a + (-1) ^ r a ^ q = 0`.
* `TauCeti.ValidLieTypeIndex.unitaryTransvectionHom`: the homomorphism `a ↦ τ_{v,a}` into
  `SU_{r+1}(q)`, for an isotropic vector `v`.

## Main results

* `TauCeti.ValidLieTypeIndex.coe_unitaryTransvectionHom` and
  `TauCeti.ValidLieTypeIndex.coe_unitaryTransvectionHom_mulVec`: the matrix of `τ_{v,a}` and its
  action `x ↦ x + a B(v, x) v`.
* `TauCeti.ValidLieTypeIndex.mul_unitaryTransvectionHom_mul_inv`: the conjugation law
  `g τ_{v,a} g⁻¹ = τ_{g v,a}`.
* `TauCeti.ValidLieTypeIndex.conj_smul_range_unitaryTransvectionHom`: conjugation by `g` carries
  the transvection subgroup of `v` to that of `g v`.
* `TauCeti.ValidLieTypeIndex.range_unitaryTransvectionHom_smul`: the transvection subgroup of `v`
  depends only on the line spanned by `v`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), the chapter on unitary groups.
* L. C. Grove, *Classical Groups and Geometric Algebra*, Graduate Studies in Mathematics 39
  (2002), the chapters on unitary groups.
-/

public section

noncomputable section

open Matrix
open scoped Pointwise

namespace TauCeti.ValidLieTypeIndex

variable {d : ValidLieTypeIndex} {r : ℕ}

/-! ### The admissible scalars -/

variable (d r) in
/-- **The scalars of the unitary transvections** of `SU_{r+1}(q)`: the elements `a` of the field
with `q²` elements with `a + (-1) ^ r a ^ q = 0`. For even `r` these are the elements of trace zero
over the field with `q` elements. -/
def unitaryTransvectionScalars :
    AddSubgroup (GaloisField d.characteristic (d.fieldExponent * 2)) where
  carrier := {a | a + (-1) ^ r * iterateFrobenius _ d.characteristic d.fieldExponent a = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    linear_combination ha + hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, mul_zero, add_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
    linear_combination -ha

/-- Membership in the admissible scalars, with `σ` written as the iterated Frobenius. -/
private theorem mem_unitaryTransvectionScalars_iff_iterateFrobenius
    {a : GaloisField d.characteristic (d.fieldExponent * 2)} :
    a ∈ unitaryTransvectionScalars d r ↔
      a + (-1) ^ r * iterateFrobenius _ d.characteristic d.fieldExponent a = 0 :=
  Iff.rfl

@[simp]
theorem mem_unitaryTransvectionScalars {a : GaloisField d.characteristic (d.fieldExponent * 2)} :
    a ∈ unitaryTransvectionScalars d r ↔ a + (-1) ^ r * a ^ d.fieldOrder = 0 := by
  have h : iterateFrobenius _ d.characteristic d.fieldExponent a = a ^ d.fieldOrder := by
    rw [coe_iterateFrobenius_galoisField]
  rw [mem_unitaryTransvectionScalars_iff_iterateFrobenius, h]

/-- Multiplying an admissible scalar by an element `t` of the field with `q` elements, `σ(t) = t`,
gives an admissible scalar. -/
private theorem mul_mem_unitaryTransvectionScalars
    {a t : GaloisField d.characteristic (d.fieldExponent * 2)}
    (ha : a ∈ unitaryTransvectionScalars d r)
    (ht : iterateFrobenius _ d.characteristic d.fieldExponent t = t) :
    a * t ∈ unitaryTransvectionScalars d r := by
  rw [mem_unitaryTransvectionScalars_iff_iterateFrobenius] at ha ⊢
  rw [map_mul, ht]
  linear_combination t * ha

/-! ### The transvection subgroups -/

variable {v : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)}

/-- A special linear matrix which is a unitary transvection along an isotropic vector, with an
admissible scalar, lies in `SU_{r+1}(q)`. -/
private theorem mem_fixedSubgroup_of_coe_eq_unitaryTransvection (hv : unitaryForm d r v v = 0)
    {a : GaloisField d.characteristic (d.fieldExponent * 2)}
    (ha : a ∈ unitaryTransvectionScalars d r)
    {g : SpecialLinearGroup (Fin (r + 1)) (GaloisField d.characteristic (d.fieldExponent * 2))}
    (hg : (g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).unitaryTransvection
          (iterateFrobenius _ d.characteristic d.fieldExponent) v a) :
    g ∈ fixedSubgroup (d.galoisFieldTwistedFrobenius r) := by
  rw [mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff, hg, ← coe_iterateFrobenius_galoisField]
  exact transpose_map_unitaryTransvection_mul_mul_self involutive_iterateFrobenius_galoisField
    transpose_map_typeAGraphConjugator_galoisField ((unitaryForm_apply v v).symm.trans hv)
    (mem_unitaryTransvectionScalars_iff_iterateFrobenius.mp ha)

/-- The unitary transvection `τ_{v,a}` along an isotropic vector `v`, with an admissible scalar
`a`, as an element of `SU_{r+1}(q)`. -/
private def unitaryTransvectionFun (v : Fin (r + 1) → GaloisField d.characteristic
    (d.fieldExponent * 2)) (hv : unitaryForm d r v v = 0) (a : unitaryTransvectionScalars d r) :
    fixedSubgroup (d.galoisFieldTwistedFrobenius r) :=
  ⟨⟨(typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).unitaryTransvection
          (iterateFrobenius _ d.characteristic d.fieldExponent) v a,
      det_unitaryTransvection ((unitaryForm_apply v v).symm.trans hv) a⟩,
    mem_fixedSubgroup_of_coe_eq_unitaryTransvection hv a.2 (rfl)⟩

variable (d) in
/-- **The unitary transvections along an isotropic vector.** For a vector `v` of
`𝔽_{q²} ^ (r + 1)` with `B(v, v) = 0`, the homomorphism `a ↦ τ_{v,a}` from the admissible scalars
`TauCeti.ValidLieTypeIndex.unitaryTransvectionScalars` to the special unitary group `SU_{r+1}(q)`,
the fixed subgroup of the graph-twisted Frobenius. Its range is the group of unitary transvections
along `v`, which is commutative by `Subgroup.range_isMulCommutative`. -/
def unitaryTransvectionHom (v : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2))
    (hv : unitaryForm d r v v = 0) :
    Multiplicative (unitaryTransvectionScalars d r) →*
      fixedSubgroup (d.galoisFieldTwistedFrobenius r) where
  toFun a := unitaryTransvectionFun v hv a.toAdd
  map_one' := Subtype.ext <| Subtype.ext <| by
    simp [unitaryTransvectionFun]
  map_mul' a b := Subtype.ext <| Subtype.ext <| by
    simp only [unitaryTransvectionFun, toAdd_mul, AddSubgroup.coe_add, Subgroup.coe_mul]
    exact (unitaryTransvection_mul_unitaryTransvection
      ((unitaryForm_apply v v).symm.trans hv) _ _).symm

/-- The matrix of the unitary transvection `τ_{v,a}` of `SU_{r+1}(q)` is `1 + a v (σ(v)ᵀ Q)`. -/
theorem coe_unitaryTransvectionHom (hv : unitaryForm d r v v = 0)
    (a : Multiplicative (unitaryTransvectionScalars d r)) :
    (d.unitaryTransvectionHom v hv a : Matrix (Fin (r + 1)) (Fin (r + 1)) _) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).unitaryTransvection
          (iterateFrobenius _ d.characteristic d.fieldExponent) v a.toAdd :=
  (rfl)

/-- The unitary transvection `τ_{v,a}` of `SU_{r+1}(q)` sends `x` to `x + a B(v, x) v`. -/
@[simp]
theorem coe_unitaryTransvectionHom_mulVec (hv : unitaryForm d r v v = 0)
    (a : Multiplicative (unitaryTransvectionScalars d r))
    (x : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    (d.unitaryTransvectionHom v hv a : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ x =
      x + ((a.toAdd : GaloisField d.characteristic (d.fieldExponent * 2)) *
        unitaryForm d r v x) • v := by
  rw [coe_unitaryTransvectionHom, unitaryTransvection_mulVec, unitaryForm_apply]

/-- **The conjugation law in `SU_{r+1}(q)`.** An element `g` conjugates the unitary transvection
`τ_{v,a}` to `τ_{g v,a}`. -/
theorem mul_unitaryTransvectionHom_mul_inv (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r))
    (hv : unitaryForm d r v v = 0)
    (hgv : unitaryForm d r ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v)
      ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v) = 0)
    (a : Multiplicative (unitaryTransvectionScalars d r)) :
    g * d.unitaryTransvectionHom v hv a * g⁻¹ =
      d.unitaryTransvectionHom ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v) hgv a := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext <| Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  exact mul_unitaryTransvection (transpose_map_mul_mul_self_of_mem g) _

/-- **The transvection subgroups are permuted by conjugation.** Conjugation by an element `g` of
`SU_{r+1}(q)` carries the subgroup of unitary transvections along `v` to the subgroup of unitary
transvections along `g v`. -/
theorem conj_smul_range_unitaryTransvectionHom
    (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r)) (hv : unitaryForm d r v v = 0)
    (hgv : unitaryForm d r ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v)
      ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v) = 0) :
    MulAut.conj g • (d.unitaryTransvectionHom v hv).range =
      (d.unitaryTransvectionHom ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ v) hgv).range := by
  ext x
  simp only [Subgroup.mem_smul_pointwise_iff_exists, MonoidHom.mem_range, MulAut.smul_def,
    MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (mul_unitaryTransvectionHom_mul_inv g hv hgv a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, mul_unitaryTransvectionHom_mul_inv g hv hgv a⟩

/-- **The transvection subgroup depends only on the line.** Rescaling an isotropic vector `v` by a
nonzero scalar `c` does not change the subgroup of unitary transvections along it, since
`τ_{c v,a} = τ_{v, a c σ(c)}` and multiplication by the nonzero norm `c σ(c)` permutes the
admissible scalars. -/
theorem range_unitaryTransvectionHom_smul (hv : unitaryForm d r v v = 0)
    {c : GaloisField d.characteristic (d.fieldExponent * 2)} (hc : c ≠ 0)
    (hcv : unitaryForm d r (c • v) (c • v) = 0) :
    (d.unitaryTransvectionHom (c • v) hcv).range = (d.unitaryTransvectionHom v hv).range := by
  -- The norm `t = c σ(c)` is nonzero and lies in the field with `q` elements.
  set t := c * iterateFrobenius _ d.characteristic d.fieldExponent c with ht_def
  have ht : iterateFrobenius _ d.characteristic d.fieldExponent t = t := by
    rw [ht_def, map_mul, involutive_iterateFrobenius_galoisField c]
    exact mul_comm _ _
  have ht₀ : t ≠ 0 := mul_ne_zero hc ((map_ne_zero _).mpr hc)
  have ht' : iterateFrobenius _ d.characteristic d.fieldExponent t⁻¹ = t⁻¹ := by
    rw [map_inv₀, ht]
  ext x
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd ⟨_, mul_mem_unitaryTransvectionScalars a.toAdd.2 ht⟩,
      Subtype.ext <| Subtype.ext ?_⟩
    simp only [coe_unitaryTransvectionHom, toAdd_ofAdd, unitaryTransvection_smul, ht_def,
      mul_assoc]
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd ⟨_, mul_mem_unitaryTransvectionScalars a.toAdd.2 ht'⟩,
      Subtype.ext <| Subtype.ext ?_⟩
    simp only [coe_unitaryTransvectionHom, toAdd_ofAdd, unitaryTransvection_smul]
    rw [mul_assoc _ c, ← ht_def, mul_assoc, inv_mul_cancel₀ ht₀, mul_one]

end TauCeti.ValidLieTypeIndex

end
