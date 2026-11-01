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
`TauCeti.ValidLieTypeIndex.unitaryForm`. Since `Qᵀ = (-1) ^ r • Q`
(`TauCeti.transpose_typeAGraphConjugator`) and the entries `0` and `±1` of `Q` are fixed by `σ`,
this form satisfies `B(y, x) = (-1) ^ r σ(B(x, y))`.

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

* `TauCeti.ValidLieTypeIndex.unitaryForm`: the form `B(x, y) = σ(x)ᵀ Q y` of `SU_{r+1}(q)`.
* `TauCeti.ValidLieTypeIndex.unitaryTransvectionScalars`: the scalars `a` with
  `a + (-1) ^ r a ^ q = 0`.
* `TauCeti.ValidLieTypeIndex.unitaryTransvectionHom`: the homomorphism `a ↦ τ_{v,a}` into
  `SU_{r+1}(q)`, for an isotropic vector `v`.

## Main results

* `TauCeti.ValidLieTypeIndex.unitaryForm_smul_left` and
  `TauCeti.ValidLieTypeIndex.unitaryForm_smul_right`: the form is semilinear in its first
  argument and linear in its second.
* `TauCeti.ValidLieTypeIndex.unitaryForm_swap`: the form is `(-1) ^ r`-Hermitian.
* `TauCeti.ValidLieTypeIndex.unitaryForm_mulVec_mulVec`: `SU_{r+1}(q)` preserves the form.
* `TauCeti.ValidLieTypeIndex.unitaryForm_single_single`: the coordinate vectors off the middle
  coordinate are isotropic.
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

/-- The `q`-power Frobenius of the field with `q²` elements is `x ↦ x ^ q`. -/
private theorem coe_iterateFrobenius_galoisField :
    ⇑(iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
      d.fieldExponent) = (· ^ d.fieldOrder) :=
  funext fun x ↦ by rw [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow]

/-- The `q`-power Frobenius of the field with `q²` elements is an involution. -/
private theorem involutive_iterateFrobenius_galoisField :
    Function.Involutive (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent) := by
  intro x
  let _ : Fintype (GaloisField d.characteristic (d.fieldExponent * 2)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField d.characteristic (d.fieldExponent * 2)) =
      d.characteristic ^ d.fieldExponent * d.characteristic ^ d.fieldExponent := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card _ _ (by have := d.fieldExponent_pos; omega),
      ← pow_add, mul_two]
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← hcard, FiniteField.pow_card]

/-- The entries `0` and `±1` of the signed reversal matrix `Q` are fixed by `σ`. -/
private theorem map_typeAGraphConjugator_galoisField :
    (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  have hmap := congrArg Units.val (map_typeAGraphConjugator
    (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
      d.fieldExponent) r)
  rwa [Units.coe_map, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply] at hmap

/-- The `σ`-sesquilinear form of Gram matrix `Q` is `(-1) ^ r`-Hermitian: `σ(Q)ᵀ = (-1) ^ r • Q`. -/
private theorem transpose_map_typeAGraphConjugator_galoisField :
    ((typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent))ᵀ =
      (-1 : GaloisField d.characteristic (d.fieldExponent * 2)) ^ r •
        (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  rw [map_typeAGraphConjugator_galoisField, transpose_typeAGraphConjugator]

/-! ### The unitary form -/

variable (d r) in
/-- **The form of the special unitary group** `SU_{r+1}(q)`: the sesquilinear form
`B(x, y) = σ(x)ᵀ Q y` on `𝔽_{q²} ^ (r + 1)`, with `σ : x ↦ x ^ q` and `Q` the signed reversal
matrix. It is semilinear in `x` and linear in `y`
(`TauCeti.ValidLieTypeIndex.unitaryForm_smul_left`,
`TauCeti.ValidLieTypeIndex.unitaryForm_smul_right`), and `B(y, x) = (-1) ^ r σ(B(x, y))`
(`TauCeti.ValidLieTypeIndex.unitaryForm_swap`). -/
def unitaryForm (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    GaloisField d.characteristic (d.fieldExponent * 2) :=
  (iterateFrobenius _ d.characteristic d.fieldExponent ∘ x) ⬝ᵥ
    ((typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ y)

theorem unitaryForm_def (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r x y =
      (iterateFrobenius _ d.characteristic d.fieldExponent ∘ x) ⬝ᵥ
        ((typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ y) :=
  (rfl)

/-- **The form is `(-1) ^ r`-Hermitian**: `B(y, x) = (-1) ^ r B(x, y) ^ q`. -/
theorem unitaryForm_swap (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r y x = (-1) ^ r * unitaryForm d r x y ^ d.fieldOrder := by
  set σ := iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
    d.characteristic d.fieldExponent with hσ_def
  set Q : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField d.characteristic (d.fieldExponent * 2)) :=
    Units.val (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)))
    with hQ_def
  have hQy : σ ∘ (Q *ᵥ y) = Q.map σ *ᵥ (σ ∘ y) := funext (RingHom.map_mulVec σ Q y)
  have hσ : σ (unitaryForm d r x y) = (-1) ^ r * unitaryForm d r y x := by
    rw [unitaryForm_def, unitaryForm_def, RingHom.map_dotProduct, hQy, hQ_def,
      map_typeAGraphConjugator_galoisField, ← Function.comp_assoc,
      involutive_iterateFrobenius_galoisField.comp_self, Function.id_comp, dotProduct_mulVec,
      ← mulVec_transpose, transpose_typeAGraphConjugator, smul_mulVec, smul_dotProduct,
      smul_eq_mul, dotProduct_comm]
  have hpow : σ (unitaryForm d r x y) = unitaryForm d r x y ^ d.fieldOrder := by
    rw [hσ_def, coe_iterateFrobenius_galoisField]
  rw [← hpow, hσ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- An element `g` of `SU_{r+1}(q)` satisfies `σ(g)ᵀ Q g = Q`. -/
private theorem transpose_map_mul_mul_self_of_mem
    (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r)) :
    ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent))ᵀ *
        (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  rw [coe_iterateFrobenius_galoisField, ← mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff]
  exact g.2

/-- **The special unitary group preserves its form**: `B(g x, g y) = B(x, y)` for every `g` in
`SU_{r+1}(q)`. -/
@[simp]
theorem unitaryForm_mulVec_mulVec (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r))
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ x)
        ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ y) =
      unitaryForm d r x y :=
  comp_mulVec_dotProduct_mulVec_mulVec (transpose_map_mul_mul_self_of_mem g) x y

/-- The form is semilinear in its first argument: `B(c x, y) = c ^ q B(x, y)`. -/
theorem unitaryForm_smul_left (c : GaloisField d.characteristic (d.fieldExponent * 2))
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r (c • x) y = c ^ d.fieldOrder * unitaryForm d r x y := by
  have hσ : iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent ∘ (c • x) =
        c ^ d.fieldOrder • (iterateFrobenius _ d.characteristic d.fieldExponent ∘ x) := by
    ext i
    rw [Function.comp_apply, Pi.smul_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      smul_eq_mul, map_mul, coe_iterateFrobenius_galoisField]
  rw [unitaryForm_def, unitaryForm_def, hσ, smul_dotProduct, smul_eq_mul]

/-- The form is linear in its second argument: `B(x, c y) = c B(x, y)`. -/
theorem unitaryForm_smul_right (c : GaloisField d.characteristic (d.fieldExponent * 2))
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r x (c • y) = c * unitaryForm d r x y := by
  rw [unitaryForm_def, unitaryForm_def, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- **Isotropic coordinate vectors.** The coordinate vector `eᵢ` is isotropic for the form
`B(x, y) = σ(x)ᵀ Q y` unless `i` is the middle coordinate `i = r - i`: the entry `Qᵢᵢ` vanishes off
the anti-diagonal. -/
theorem unitaryForm_single_single {i : Fin (r + 1)} (hi : i ≠ i.rev) :
    unitaryForm d r (Pi.single i 1) (Pi.single i 1) = 0 := by
  have hσ : iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent ∘ Pi.single i 1 = Pi.single i 1 := by
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  rw [unitaryForm_def, hσ, mulVec_single_one, single_dotProduct, one_mul, col_apply,
    typeAGraphConjugator_apply]
  simp only [hi, ↓reduceIte]

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
  zero_mem' := by simp
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
    transpose_map_typeAGraphConjugator_galoisField hv
    (mem_unitaryTransvectionScalars_iff_iterateFrobenius.mp ha)

/-- The unitary transvection `τ_{v,a}` along an isotropic vector `v`, with an admissible scalar
`a`, as an element of `SU_{r+1}(q)`. -/
private def unitaryTransvectionFun (v : Fin (r + 1) → GaloisField d.characteristic
    (d.fieldExponent * 2)) (hv : unitaryForm d r v v = 0) (a : unitaryTransvectionScalars d r) :
    fixedSubgroup (d.galoisFieldTwistedFrobenius r) :=
  ⟨⟨(typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).unitaryTransvection
          (iterateFrobenius _ d.characteristic d.fieldExponent) v a,
      det_unitaryTransvection hv a⟩,
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
    simp only [unitaryTransvectionFun, toAdd_mul, AddSubgroup.coe_add, Subgroup.coe_mul,
      SpecialLinearGroup.coe_mk]
    exact (unitaryTransvection_mul_unitaryTransvection hv _ _).symm

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
  rw [coe_unitaryTransvectionHom, unitaryTransvection_mulVec, unitaryForm_def]

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
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, coe_unitaryTransvectionHom]
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
