/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.OrthogonalGroup
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Quaternary
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

import Mathlib.Algebra.BigOperators.Pi

/-!
# The triality isometry of `D₄`

The Dynkin diagram of `D₄` has a rotation of order three fixing the central node and cycling the
three outer nodes, the diagram symmetry `TauCeti.trialityPermD4`. In the Conway--Sloane
coordinates `D₄ = {x ∈ ℤ⁴ | ∑ xᵢ even}` it is induced by the rational orthogonal map

```text
τ(x) = (h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃),    h = (x₀ + x₁ + x₂ + x₃) / 2,
```

which sends the Bourbaki simple roots `α₁ ↦ α₃ ↦ α₄ ↦ α₁` and fixes `α₂`. It preserves `D₄`, and
on the discriminant group it cycles the three nonzero classes,

```text
v ↦ c ↦ s ↦ v,
```

where `v`, `s`, `c` are the vector, spinor and cospinor classes. Under the identification of the
`D₄` glue labels `0, s, v, c` with `0, ω, 1, ω²` in a field `F₄` of four elements, this is
multiplication by `ω²`, and `τ² = τ⁻¹` is multiplication by `ω`. Triality is what lets the
`F₄`-scalar symmetries of a quaternary glue code, such as the coordinate scalings of the hexacode,
act on a lattice glued from copies of `D₄`.

## Main declarations

* `TauCeti.IntegralLattice.checkerboardTriality`: the isometry `τ` of the checkerboard lattice
  `D₄`, with coordinate formula `checkerboardTriality_apply`.
* `TauCeti.IntegralLattice.checkerboardTriality_checkerboardSimpleRoot`: `τ` permutes the simple
  roots by `trialityPermD4`.
* `TauCeti.IntegralLattice.checkerboardTriality_pow_three`,
  `TauCeti.IntegralLattice.orderOf_checkerboardTriality`: `τ` has order `3`.
* `discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass` and its two companions:
  `τ` acts on the discriminant classes by `v ↦ c ↦ s ↦ v`.
* `discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry`:
  in the quaternary coordinates of the discriminant group, `τ` is multiplication by `ω²`, and its
  powers give `TauCeti.IntegralLattice.checkerboardScalarIsometry`, realizing every unit of `F₄` on
  the checkerboard discriminant group.
* `TauCeti.DynkinType.typeD4Triality`: the triality isometry of the root lattice of type `D₄`,
  permuting the simple-root coordinates by `trialityPermD4` (`typeD4Triality_single`,
  `typeD4Triality_apply_eq`), of order `3` (`orderOf_typeD4Triality`).
* `TauCeti.DynkinType.typeD4GlueAlphabetTriality`, `TauCeti.DynkinType.trialityGlueLabelPerm`:
  the induced isometry of the `D₄` glue alphabet, cycling the Conway--Sloane labels
  `1 ↦ 2 ↦ 3 ↦ 1` (`typeD4GlueAlphabetTriality_glueLabelEquiv`) and compatible with
  `glueAlphabetIsometry` (`glueAlphabetIsometry_typeD4GlueAlphabetTriality`).
* `TauCeti.DynkinType.discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry`: on the `D₄` glue
  alphabet, read in `F₄`, it is multiplication by `ω²`; its powers give every nonzero scaling
  (`discriminantGroupEquiv_typeD4Triality_pow_glueAlphabetIsometry`).
* `TauCeti.DynkinType.typeD4ScalarIsometry`: the power of triality realizing a given unit of
  `F₄` on the glue alphabet (`typeD4ScalarIsometry_eq_pow`), compatible with
  `checkerboardScalarIsometry` under `rootLatticeIsometryCheckerboard`
  (`typeD4ScalarIsometry_eq_conjMulEquiv`,
  `rootLatticeIsometryCheckerboard_typeD4ScalarIsometry_apply`).

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7.1, and Chapter 7, §§8–9.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

namespace TauCeti

namespace IntegralLattice

/-! ## Triality on the checkerboard lattice -/

/-- The linear map underlying triality on `ℚ⁴`. -/
private def trialityLinearMap : (Fin 4 → ℚ) →ₗ[ℚ] Fin 4 → ℚ where
  toFun x := ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
    (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem trialityLinearMap_apply (x : Fin 4 → ℚ) :
    trialityLinearMap x = ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
      (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2] :=
  (rfl)

/-- Triality has order three on `ℚ⁴`. -/
private theorem trialityLinearMap_apply_apply_apply (x : Fin 4 → ℚ) :
    trialityLinearMap (trialityLinearMap (trialityLinearMap x)) = x := by
  ext i
  fin_cases i <;> simp [trialityLinearMap_apply] <;> ring

/-- Triality on `ℚ⁴` as a linear equivalence, with inverse its square. -/
private def trialityLinearEquiv : (Fin 4 → ℚ) ≃ₗ[ℚ] Fin 4 → ℚ :=
  LinearEquiv.ofLinearMap trialityLinearMap (trialityLinearMap ∘ₗ trialityLinearMap)
    (LinearMap.ext trialityLinearMap_apply_apply_apply)
    (LinearMap.ext trialityLinearMap_apply_apply_apply)

private theorem trialityLinearEquiv_apply (x : Fin 4 → ℚ) :
    trialityLinearEquiv x = trialityLinearMap x :=
  (rfl)

/-- Triality maps the checkerboard carrier into itself: with `h` half the coordinate sum, the
image `(h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃)` is integral, of coordinate sum `2 (h - x₃)`. -/
private theorem trialityLinearMap_mem_checkerboardCarrier {x : Fin 4 → ℚ}
    (hx : x ∈ checkerboardCarrier 4) : trialityLinearMap x ∈ checkerboardCarrier 4 := by
  obtain ⟨hxZ, m, hm⟩ := (mem_checkerboardCarrier_iff x).1 hx
  choose z hz using hxZ
  simp only [Fin.sum_univ_four, hz] at hm
  have hm' : z 0 + z 1 + z 2 + z 3 = 2 * m := by exact_mod_cast hm
  refine mem_checkerboardCarrier_of ![m, m - z 2 - z 3, m - z 1 - z 3, m - z 0 - z 3]
    (fun i ↦ ?_) ⟨m - z 3, by simp only [Fin.sum_univ_four]; simp; linear_combination -hm'⟩
  fin_cases i <;> simp [trialityLinearMap_apply, hz] <;> linarith

/-- Triality preserves the dot product on `ℚ⁴`. -/
private theorem sum_trialityLinearMap_mul_trialityLinearMap (x y : Fin 4 → ℚ) :
    ∑ i, trialityLinearMap x i * trialityLinearMap y i = ∑ i, x i * y i := by
  simp only [Fin.sum_univ_four, trialityLinearMap_apply]
  simp
  ring

/-- **The triality isometry of `D₄`**: the isometry of the checkerboard lattice of rank four
given by `x ↦ (h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃)`, where `h = (x₀ + x₁ + x₂ + x₃) / 2`.
It permutes the simple roots by the diagram symmetry `trialityPermD4`
(`checkerboardTriality_checkerboardSimpleRoot`) and cycles the nonzero discriminant classes
`v ↦ c ↦ s ↦ v`. -/
noncomputable def checkerboardTriality :
    Isometry (checkerboardLattice 4) (checkerboardLattice 4) where
  toIsometryEquiv :=
    { toLinearEquiv := trialityLinearEquiv
      map_app' x y := by
        rw [checkerboardLattice_form_apply, checkerboardLattice_form_apply]
        simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, trialityLinearEquiv_apply]
        exact sum_trialityLinearMap_mul_trialityLinearMap x y }
  map_carrier := by
    rw [checkerboardLattice_carrier]
    -- Images under the `ℤ`-restriction of the isometry structure under construction unfold
    -- definitionally to `trialityLinearMap`, so both inclusions are proved with the
    -- `trialityLinearMap` lemmas.
    refine le_antisymm ?_ fun x hx ↦ ⟨trialityLinearMap (trialityLinearMap x),
      trialityLinearMap_mem_checkerboardCarrier (trialityLinearMap_mem_checkerboardCarrier hx),
      trialityLinearMap_apply_apply_apply x⟩
    rintro _ ⟨x, hx, rfl⟩
    exact trialityLinearMap_mem_checkerboardCarrier hx

private theorem checkerboardTriality_eq_trialityLinearMap (x : Fin 4 → ℚ) :
    checkerboardTriality x = trialityLinearMap x :=
  (rfl)

/-- The coordinate formula of triality: the matrix `½ [[1, 1, 1, 1], [1, 1, -1, -1],
[1, -1, 1, -1], [-1, 1, 1, -1]]`. -/
@[simp]
theorem checkerboardTriality_apply (x : Fin 4 → ℚ) :
    checkerboardTriality x = ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
      (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2] :=
  (rfl)

/-- **Triality is the diagram rotation of `D₄`**: it permutes the simple roots by
`trialityPermD4`, sending the Bourbaki simple roots `α₁ ↦ α₃ ↦ α₄ ↦ α₁` and fixing the central
root `α₂`. -/
theorem checkerboardTriality_checkerboardSimpleRoot (i : Fin 4) :
    checkerboardTriality (checkerboardSimpleRoot 4 le_rfl i) =
      checkerboardSimpleRoot 4 le_rfl (trialityPermD4 i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num

/-- **Triality has order three.** -/
@[simp]
theorem checkerboardTriality_pow_three : checkerboardTriality ^ 3 = 1 :=
  Isometry.ext fun x ↦ by
    simp only [pow_three, Isometry.mul_apply, Isometry.one_apply,
      checkerboardTriality_eq_trialityLinearMap]
    exact trialityLinearMap_apply_apply_apply x

/-- Triality moves the first simple root, so it is not the identity. -/
theorem checkerboardTriality_ne_one : checkerboardTriality ≠ 1 := fun h ↦ by
  have h0 := congrArg (fun f : Isometry (checkerboardLattice 4) (checkerboardLattice 4) ↦
    f (checkerboardSimpleRoot 4 le_rfl 0) 0) h
  rw [checkerboardTriality_checkerboardSimpleRoot, Isometry.one_apply] at h0
  norm_num at h0

/-- **Triality has order exactly three.** -/
@[simp]
theorem orderOf_checkerboardTriality : orderOf checkerboardTriality = 3 :=
  orderOf_eq_prime checkerboardTriality_pow_three checkerboardTriality_ne_one

/-! ## The action on the discriminant group -/

/-- Triality sends the vector class to the cospinor class. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardVectorClass 4) =
      checkerboardCospinorClass 4 := by
  rw [← (mk_eq_checkerboardVectorClass_iff ⟨_, checkerboardVector_mem_dualCarrier⟩).2
      (by simp), Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardCospinorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of ![0, -1, -1, 0] (fun i ↦ ?_) ⟨-1, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- Triality sends the spinor class to the vector class. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardSpinorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardSpinorClass 4) =
      checkerboardVectorClass 4 := by
  rw [checkerboardSpinorClass_def, Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardVectorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of ![1, 0, 0, -1] (fun i ↦ ?_) ⟨0, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- Triality sends the cospinor class to the spinor class: it maps the cospinor vector
`(½, ½, ½, -½)` to the spinor vector `(½, ½, ½, ½)`. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardCospinorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardCospinorClass 4) =
      checkerboardSpinorClass 4 := by
  rw [← (mk_eq_checkerboardCospinorClass_iff ⟨_, checkerboardCospinor_mem_dualCarrier⟩).2
      (by simp), Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardSpinorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of 0 (fun i ↦ ?_) ⟨0, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-- **Triality is multiplication by `ω²`** on the discriminant group of `D₄`, read in the
quaternary coordinates sending `1, ω, ω²` to the vector, spinor and cospinor classes. -/
theorem discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry
    (y : F) :
    checkerboardTriality.discriminantGroupEquiv
        (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω y) =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (ω ^ 2 * y) := by
  obtain ⟨i, rfl⟩ := (finFourEquiv hF hω).surjective y
  have hω3 := pow_three_eq_one_of_sq_add_self_add_one_eq_zero hω
  have hω₁ : ω ^ 2 * ω = 1 := by linear_combination hω3
  have hω₂ : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω3
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, finFourEquiv_apply,
    Matrix.cons_val]
  -- The quaternary isometry takes values in the carrier of the discriminant quadratic module,
  -- which is the discriminant group only up to unfolding, so the class computations above are
  -- applied with `exact` rather than `rw`.
  · rw [mul_zero, map_zero]
    exact checkerboardTriality.discriminantGroupEquiv.map_zero
  · rw [mul_one, typeD4QuaternaryDiscriminantQuadraticIsometry_one,
      typeD4QuaternaryDiscriminantQuadraticIsometry_root_sq]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass
  · rw [hω₁, typeD4QuaternaryDiscriminantQuadraticIsometry_root,
      typeD4QuaternaryDiscriminantQuadraticIsometry_one]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardSpinorClass
  · rw [hω₂, typeD4QuaternaryDiscriminantQuadraticIsometry_root_sq,
      typeD4QuaternaryDiscriminantQuadraticIsometry_root]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardCospinorClass

/-- **The powers of triality act on the discriminant group of `D₄` as multiplication by the powers
of `ω²`**, read in the quaternary coordinates `typeD4QuaternaryDiscriminantQuadraticIsometry`. -/
theorem
    discriminantGroupEquiv_checkerboardTriality_pow_typeD4QuaternaryDiscriminantQuadraticIsometry
    (k : ℕ) (y : F) :
    (checkerboardTriality ^ k).discriminantGroupEquiv
        (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω y) =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω ((ω ^ 2) ^ k * y) := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, Isometry.one_def, Isometry.discriminantGroupEquiv_refl]
    -- `LinearEquiv.refl_apply` does not rewrite here: the argument is typed in the carrier of
    -- the discriminant quadratic module rather than in the discriminant group.
    rfl
  | succ k ih =>
    rw [pow_succ checkerboardTriality k, Isometry.mul_def, Isometry.discriminantGroupEquiv_trans]
    refine (congrArg _
      (discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry
        hF hω y)).trans ((ih _).trans ?_)
    rw [pow_succ (ω ^ 2) k, mul_assoc]

/-- **Triality realizes every nonzero scalar of `F₄` on the checkerboard `D₄` discriminant group.**
For a unit `a` of a field `F` of four elements, this is the power of `checkerboardTriality` acting
on the discriminant group, read in the quaternary coordinates
`typeD4QuaternaryDiscriminantQuadraticIsometry`, as multiplication by `a`. For `a = 1, ω, ω²` it is
the power `0, 2, 1` of triality. -/
noncomputable def checkerboardScalarIsometry (a : Fˣ) :
    Isometry (checkerboardLattice 4) (checkerboardLattice 4) :=
  checkerboardTriality ^ ![0, 0, 2, 1] ((finFourEquiv hF hω).symm a)

/-- **`checkerboardScalarIsometry a` acts on the `D₄` discriminant group as multiplication by
`a`**, read through `typeD4QuaternaryDiscriminantQuadraticIsometry`. -/
theorem
    discriminantGroupEquiv_checkerboardScalarIsometry_typeD4QuaternaryDiscriminantQuadraticIsometry
    (a : Fˣ) (y : F) :
    (checkerboardScalarIsometry hF hω a).discriminantGroupEquiv
        (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω y) =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (a * y) := by
  rw [checkerboardScalarIsometry,
    discriminantGroupEquiv_checkerboardTriality_pow_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω,
    sq_pow_finFourEquiv_symm]

/-- **`checkerboardScalarIsometry a` is the power of triality realizing `a`**: if `(ω²)ᵏ = a`, then
it is `checkerboardTriality ^ k`. -/
theorem checkerboardScalarIsometry_eq_pow (a : Fˣ) {k : ℕ} (hk : (ω ^ 2) ^ k = a) :
    checkerboardScalarIsometry hF hω a = checkerboardTriality ^ k := by
  -- Both `ω²` and triality have order three, so only the exponent modulo three matters.
  have h3 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_three_eq_one_of_sq_add_self_add_one_eq_zero hω,
      one_pow]
  have h1 : ω ^ 2 ≠ 1 := fun h ↦ one_ne_zero (α := F) <| by
    linear_combination ω * hω - (ω + 1) * h - ω * two_eq_zero_of_natCard_eq_four hF
  have hmod := (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩).pow_inj_mod.mp
    ((sq_pow_finFourEquiv_symm hF hω a).trans hk.symm)
  rw [orderOf_eq_prime h3 h1] at hmod
  exact (pow_eq_pow_mod _ checkerboardTriality_pow_three).trans
    ((congrArg _ hmod).trans (pow_eq_pow_mod k checkerboardTriality_pow_three).symm)

/-- The scalar `1` is realized on the checkerboard lattice by the identity isometry. -/
@[simp]
theorem checkerboardScalarIsometry_one : checkerboardScalarIsometry hF hω 1 = 1 :=
  (checkerboardScalarIsometry_eq_pow hF hω 1 (k := 0) (by rw [pow_zero, Units.val_one])).trans
    (pow_zero _)

/-- The checkerboard isometries realizing two scalars compose to the isometry realizing their
product. -/
theorem checkerboardScalarIsometry_mul (a b : Fˣ) :
    checkerboardScalarIsometry hF hω (a * b) =
      checkerboardScalarIsometry hF hω a * checkerboardScalarIsometry hF hω b := by
  rw [checkerboardScalarIsometry_eq_pow hF hω a (sq_pow_finFourEquiv_symm hF hω a),
    checkerboardScalarIsometry_eq_pow hF hω b (sq_pow_finFourEquiv_symm hF hω b), ← pow_add]
  refine checkerboardScalarIsometry_eq_pow hF hω _ ?_
  rw [pow_add, sq_pow_finFourEquiv_symm, sq_pow_finFourEquiv_symm, Units.val_mul]

/-- The checkerboard isometry realizing the inverse of a scalar is the inverse self-isometry. -/
@[simp]
theorem checkerboardScalarIsometry_inv (a : Fˣ) :
    checkerboardScalarIsometry hF hω a⁻¹ = (checkerboardScalarIsometry hF hω a)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp <|
    (checkerboardScalarIsometry_mul hF hω a⁻¹ a).symm.trans <| by
      rw [inv_mul_cancel, checkerboardScalarIsometry_one]

end IntegralLattice

/-! ## Triality on the root lattice of type `D₄` -/

namespace DynkinType

open IntegralLattice

variable (ht : (D 4).IsSimplyLaced)

/-- **The triality isometry of the root lattice of type `D₄`**: `checkerboardTriality`,
transported along the identification `rootLatticeIsometryCheckerboard` with the checkerboard
lattice. It is the diagram rotation of `D₄`, permuting the simple-root coordinates by
`trialityPermD4` (`typeD4Triality_single`). -/
noncomputable def typeD4Triality : Isometry ((D 4).rootLattice ht) ((D 4).rootLattice ht) :=
  (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.conjMulEquiv checkerboardTriality

/-- Triality on the root lattice is triality on the checkerboard lattice, conjugated by
`rootLatticeIsometryCheckerboard`. -/
theorem typeD4Triality_apply (x : Fin (D 4).rank → ℚ) :
    typeD4Triality ht x = (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm
      (checkerboardTriality (rootLatticeIsometryCheckerboard 4 le_rfl ht x)) := by
  rw [typeD4Triality, Isometry.conjMulEquiv_apply, Isometry.symm_symm]

/-- **Triality permutes the simple roots of `D₄` by `trialityPermD4`**: `α₁ ↦ α₃ ↦ α₄ ↦ α₁`,
fixing `α₂`. -/
-- Not a `simp` lemma: `rank_D` rewrites the index type `Fin (D 4).rank` of `Pi.single`, so the
-- statement is not in simp-normal form.
theorem typeD4Triality_single (i : Fin 4) :
    typeD4Triality ht (Pi.single i 1) = Pi.single (trialityPermD4 i) 1 := by
  rw [typeD4Triality_apply, rootLatticeIsometryCheckerboard_single,
    checkerboardTriality_checkerboardSimpleRoot,
    ← rootLatticeIsometryCheckerboard_single 4 le_rfl ht, Isometry.symm_apply_apply]
  -- The two sides differ only in spelling the index type as `Fin 4` or `Fin (D 4).rank`.
  rfl

/-- **Simple-root coordinates of triality on `D₄`**: the `j`-th Bourbaki simple-root coordinate of
`typeD4Triality ht x` is read from `trialityPermD4.symm j`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside `x` by `rank_D`.
theorem typeD4Triality_apply_eq (x : Fin (D 4).rank → ℚ) (j : Fin 4) :
    typeD4Triality ht x j = x (trialityPermD4.symm j) := by
  let e : (Fin 4 → ℚ) ≃ₗ[ℚ] Fin 4 → ℚ := (typeD4Triality ht).toIsometryEquiv.toLinearEquiv
  let y : Fin 4 → ℚ := x
  obtain ⟨k, rfl⟩ := trialityPermD4.surjective j
  change e y (trialityPermD4 k) = y (trialityPermD4.symm (trialityPermD4 k))
  conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
  have hsum : ∑ i : Fin 4, e (y i • Pi.single i 1) (trialityPermD4 k) =
      ∑ i : Fin 4, (y i • Pi.single (trialityPermD4 i) (1 : ℚ)) (trialityPermD4 k) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [map_smul]
      exact congrArg (fun v : Fin 4 → ℚ ↦ (y i • v) (trialityPermD4 k))
        (typeD4Triality_single ht i)
  rw [hsum]
  simp only [Pi.smul_apply, Pi.single_apply, trialityPermD4.injective.eq_iff, smul_eq_mul,
    mul_boole, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Equiv.symm_apply_apply]

/-- **Triality has order three.** -/
@[simp]
theorem typeD4Triality_pow_three : typeD4Triality ht ^ 3 = 1 := by
  rw [typeD4Triality, ← map_pow, checkerboardTriality_pow_three, map_one]

/-- Triality on the `D₄` root lattice is not the identity. -/
theorem typeD4Triality_ne_one : typeD4Triality ht ≠ 1 :=
  (MulEquiv.map_ne_one_iff _).mpr checkerboardTriality_ne_one

/-- **Triality on the `D₄` root lattice has order exactly three.** -/
@[simp]
theorem orderOf_typeD4Triality : orderOf (typeD4Triality ht) = 3 :=
  orderOf_eq_prime (typeD4Triality_pow_three ht) (typeD4Triality_ne_one ht)

/-- **The permutation of the `D₄` Conway--Sloane glue labels induced by triality**: it fixes `0`
and cycles `1 ↦ 2 ↦ 3 ↦ 1`, sending spinor `[1]` to vector `[2]`, vector `[2]` to cospinor `[3]`,
and cospinor `[3]` to spinor `[1]`. -/
def trialityGlueLabelPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 3 * Equiv.swap 1 2

/-- Triality fixes the zero glue label of `D₄`. -/
@[simp] lemma trialityGlueLabelPerm_apply_zero : trialityGlueLabelPerm 0 = 0 := by decide
/-- Triality sends the spinor label `[1]` of `D₄` to the vector label `[2]`. -/
@[simp] lemma trialityGlueLabelPerm_apply_one : trialityGlueLabelPerm 1 = 2 := by decide
/-- Triality sends the vector label `[2]` of `D₄` to the cospinor label `[3]`. -/
@[simp] lemma trialityGlueLabelPerm_apply_two : trialityGlueLabelPerm 2 = 3 := by decide
/-- Triality sends the cospinor label `[3]` of `D₄` to the spinor label `[1]`. -/
@[simp] lemma trialityGlueLabelPerm_apply_three : trialityGlueLabelPerm 3 = 1 := by decide

/-- Applying `trialityGlueLabelPerm` three times is the identity. -/
@[simp]
theorem trialityGlueLabelPerm_pow_three : trialityGlueLabelPerm ^ 3 = 1 := by decide

/-- Applying `trialityGlueLabelPerm` three times fixes every `D₄` glue label. -/
@[simp]
theorem trialityGlueLabelPerm_apply_apply_apply (i : Fin 4) :
    trialityGlueLabelPerm (trialityGlueLabelPerm (trialityGlueLabelPerm i)) = i := by
  fin_cases i <;> decide

/-- `trialityGlueLabelPerm` has order three. -/
@[simp]
theorem orderOf_trialityGlueLabelPerm : orderOf trialityGlueLabelPerm = 3 :=
  orderOf_eq_prime trialityGlueLabelPerm_pow_three (by decide)

/-- **The triality isometry of the `D₄` glue alphabet**: the quadratic-module self-isometry of
`(D 4).glueAlphabet ht` induced by `typeD4Triality ht` through `(D 4).glueAlphabetIsometry`. -/
noncomputable def typeD4GlueAlphabetTriality :
    FiniteQuadraticModule.Isometry ((D 4).glueAlphabet ht) ((D 4).glueAlphabet ht) :=
  ((D 4).glueAlphabetIsometry (valid_D.mpr (by decide)) ht).trans <|
    ((typeD4Triality ht).discriminantQuadraticIsometry ((D 4).isEven_rootLattice ht)).trans
      ((D 4).glueAlphabetIsometry (valid_D.mpr (by decide)) ht).symm

/-- **`typeD4GlueAlphabetTriality` is the glue-alphabet action of `typeD4Triality`**: it commutes
with `glueAlphabetIsometry` and `(typeD4Triality ht).discriminantQuadraticIsometry`. -/
theorem glueAlphabetIsometry_typeD4GlueAlphabetTriality (hv : (D 4).Valid)
    (x : (D 4).glueAlphabet ht) :
    (D 4).glueAlphabetIsometry hv ht (typeD4GlueAlphabetTriality ht x) =
      (typeD4Triality ht).discriminantQuadraticIsometry ((D 4).isEven_rootLattice ht)
        ((D 4).glueAlphabetIsometry hv ht x) := by
  obtain rfl : hv = valid_D.mpr (by decide) := Subsingleton.elim _ _
  exact QuadraticMap.IsometryEquiv.apply_symm_apply _ _

/-- **Triality permutes the Conway--Sloane labels of `D₄` by `trialityGlueLabelPerm`**, fixing
`[0]` and cycling `[1] ↦ [2] ↦ [3] ↦ [1]`. -/
@[simp]
theorem typeD4GlueAlphabetTriality_glueLabelEquiv (i : Fin 4) :
    typeD4GlueAlphabetTriality ht ((D 4).glueLabelEquiv ht i) =
      (D 4).glueLabelEquiv ht (trialityGlueLabelPerm i) := by
  have hv : (D 4).Valid := valid_D.mpr (by decide)
  apply EquivLike.injective ((D 4).glueAlphabetIsometry hv ht)
  rw [glueAlphabetIsometry_typeD4GlueAlphabetTriality ht hv]
  refine (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans ?_
  rw [glueAlphabetIsometry_D_apply_of_even 4 hv ht (by decide),
    glueAlphabetIsometry_D_apply_of_even 4 hv ht (by decide), typeD4Triality]
  refine (Isometry.discriminantGroupEquiv_conjMulEquiv_apply _ _ _).trans (congrArg _ ?_)
  rw [glueLabelEquiv_D_of_even 4 ht (by decide), glueLabelEquiv_D_of_even 4 ht (by decide)]
  fin_cases i <;> simp [Prod.mk_zero_zero,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one]

/-- Reading Conway--Sloane labels after `typeD4GlueAlphabetTriality` applies
`trialityGlueLabelPerm`. -/
@[simp]
theorem glueLabelEquiv_symm_typeD4GlueAlphabetTriality (x : (D 4).glueAlphabet ht) :
    ((D 4).glueLabelEquiv ht).symm (typeD4GlueAlphabetTriality ht x) =
      trialityGlueLabelPerm (((D 4).glueLabelEquiv ht).symm x) := by
  obtain ⟨i, rfl⟩ := ((D 4).glueLabelEquiv ht).surjective x
  rw [typeD4GlueAlphabetTriality_glueLabelEquiv, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Applying `typeD4GlueAlphabetTriality` three times fixes every element of the `D₄` glue
alphabet. -/
@[simp]
theorem typeD4GlueAlphabetTriality_apply_apply_apply (x : (D 4).glueAlphabet ht) :
    typeD4GlueAlphabetTriality ht
        (typeD4GlueAlphabetTriality ht (typeD4GlueAlphabetTriality ht x)) = x := by
  obtain ⟨i, rfl⟩ := ((D 4).glueLabelEquiv ht).surjective x
  rw [typeD4GlueAlphabetTriality_glueLabelEquiv, typeD4GlueAlphabetTriality_glueLabelEquiv,
    typeD4GlueAlphabetTriality_glueLabelEquiv, trialityGlueLabelPerm_apply_apply_apply]

variable (hv : (D 4).Valid) {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F}
  (hω : ω ^ 2 + ω + 1 = 0)

/-- **Triality acts on the `D₄` glue alphabet as multiplication by `ω²`**: read through the
identification `typeD4GlueAlphabetQuaternaryIsometry` of the labels `0, s, v, c` with
`0, ω, 1, ω²`, the induced action of `typeD4Triality` on the discriminant group is `y ↦ ω² y`. -/
theorem discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry
    (x : (D 4).glueAlphabet ht) :
    (typeD4Triality ht).discriminantGroupEquiv ((D 4).glueAlphabetIsometry hv ht x) =
      (D 4).glueAlphabetIsometry hv ht ((typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (ω ^ 2 * typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
  -- Both glue identifications factor through the quaternary coordinates of the checkerboard
  -- discriminant group.
  rw [glueAlphabetIsometry_D_four_apply hF hω, glueAlphabetIsometry_D_four_apply hF hω]
  refine (Isometry.discriminantGroupEquiv_conjMulEquiv_apply _ _ _).trans (congrArg _ ((
    discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω _).trans ?_))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- Read through `typeD4GlueAlphabetQuaternaryIsometry`, `typeD4GlueAlphabetTriality` multiplies by
`ω²`. -/
@[simp]
theorem typeD4GlueAlphabetQuaternaryIsometry_typeD4GlueAlphabetTriality
    (x : (D 4).glueAlphabet ht) :
    typeD4GlueAlphabetQuaternaryIsometry hF hω (typeD4GlueAlphabetTriality ht x) =
      ω ^ 2 * typeD4GlueAlphabetQuaternaryIsometry hF hω x := by
  have hv : (D 4).Valid := valid_D.mpr (by decide)
  apply EquivLike.injective (typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
  rw [QuadraticMap.IsometryEquiv.symm_apply_apply]
  apply EquivLike.injective ((D 4).glueAlphabetIsometry hv ht)
  exact (glueAlphabetIsometry_typeD4GlueAlphabetTriality ht hv x).trans <|
    (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
      (discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry ht hv hF hω x)

/-- **The powers of triality act on the `D₄` glue alphabet as multiplication by the powers of
`ω²`**, read through `typeD4GlueAlphabetQuaternaryIsometry`. Every nonzero element of `F₄` is a
power of `ω²`, so every nonzero scaling of the quaternary alphabet is induced by an isometry of the
root lattice. -/
theorem discriminantGroupEquiv_typeD4Triality_pow_glueAlphabetIsometry (k : ℕ)
    (x : (D 4).glueAlphabet ht) :
    (typeD4Triality ht ^ k).discriminantGroupEquiv ((D 4).glueAlphabetIsometry hv ht x) =
      (D 4).glueAlphabetIsometry hv ht ((typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        ((ω ^ 2) ^ k * typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
  rw [typeD4Triality, ← map_pow, glueAlphabetIsometry_D_four_apply hF hω,
    glueAlphabetIsometry_D_four_apply hF hω]
  refine (Isometry.discriminantGroupEquiv_conjMulEquiv_apply _ _ _).trans (congrArg _ ((
    discriminantGroupEquiv_checkerboardTriality_pow_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω k _).trans ?_))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- **Triality realizes every nonzero scalar of `F₄` on the `D₄` glue alphabet.** For a unit `a`
of a field `F` of four elements, this is the power of `typeD4Triality` acting on the glue
alphabet, read in `F` through `typeD4GlueAlphabetQuaternaryIsometry`, as multiplication by `a`
(`discriminantGroupEquiv_typeD4ScalarIsometry_glueAlphabetIsometry`). For `a = 1, ω, ω²` it is
the power `0, 2, 1` of triality. -/
noncomputable def typeD4ScalarIsometry (a : Fˣ) :
    Isometry ((D 4).rootLattice ht) ((D 4).rootLattice ht) :=
  typeD4Triality ht ^ ![0, 0, 2, 1] ((finFourEquiv hF hω).symm a)

/-- `typeD4ScalarIsometry a` is `checkerboardScalarIsometry a`, conjugated along
`rootLatticeIsometryCheckerboard`. -/
theorem typeD4ScalarIsometry_eq_conjMulEquiv (a : Fˣ) :
    typeD4ScalarIsometry ht hF hω a =
      (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.conjMulEquiv
        (checkerboardScalarIsometry hF hω a) := by
  rw [typeD4ScalarIsometry, checkerboardScalarIsometry, typeD4Triality, map_pow]

/-- `typeD4ScalarIsometry a` acts on the root lattice by conjugating `checkerboardScalarIsometry a`
with `rootLatticeIsometryCheckerboard`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the argument `x` by `rank_D`.
theorem typeD4ScalarIsometry_apply (a : Fˣ) (x : Fin (D 4).rank → ℚ) :
    typeD4ScalarIsometry ht hF hω a x = (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm
      (checkerboardScalarIsometry hF hω a (rootLatticeIsometryCheckerboard 4 le_rfl ht x)) := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, Isometry.conjMulEquiv_apply, Isometry.symm_symm]

/-- **`rootLatticeIsometryCheckerboard` intertwines `typeD4ScalarIsometry` and
`checkerboardScalarIsometry` pointwise.** -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the argument `x` by `rank_D`.
theorem rootLatticeIsometryCheckerboard_typeD4ScalarIsometry_apply (a : Fˣ)
    (x : Fin (D 4).rank → ℚ) :
    rootLatticeIsometryCheckerboard 4 le_rfl ht (typeD4ScalarIsometry ht hF hω a x) =
      checkerboardScalarIsometry hF hω a (rootLatticeIsometryCheckerboard 4 le_rfl ht x) := by
  rw [typeD4ScalarIsometry_apply, Isometry.apply_symm_apply]

/-- **`typeD4ScalarIsometry a` acts on the `D₄` glue alphabet as multiplication by `a`**, read
through `typeD4GlueAlphabetQuaternaryIsometry`. -/
theorem discriminantGroupEquiv_typeD4ScalarIsometry_glueAlphabetIsometry (a : Fˣ)
    (x : (D 4).glueAlphabet ht) :
    (typeD4ScalarIsometry ht hF hω a).discriminantGroupEquiv
        ((D 4).glueAlphabetIsometry hv ht x) =
      (D 4).glueAlphabetIsometry hv ht ((typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (a * typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, glueAlphabetIsometry_D_four_apply hF hω,
    glueAlphabetIsometry_D_four_apply hF hω]
  refine (Isometry.discriminantGroupEquiv_conjMulEquiv_apply _ _ _).trans (congrArg _ ((
    discriminantGroupEquiv_checkerboardScalarIsometry_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω a _).trans ?_))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- **`typeD4ScalarIsometry a` is the power of triality realizing `a`**: if `(ω²)ᵏ = a`, then it
is `typeD4Triality ^ k`. -/
theorem typeD4ScalarIsometry_eq_pow (a : Fˣ) {k : ℕ} (hk : (ω ^ 2) ^ k = a) :
    typeD4ScalarIsometry ht hF hω a = typeD4Triality ht ^ k := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, checkerboardScalarIsometry_eq_pow hF hω a hk,
    map_pow, typeD4Triality]

/-- The scalar `1` is realized by the identity isometry. -/
@[simp]
theorem typeD4ScalarIsometry_one : typeD4ScalarIsometry ht hF hω 1 = 1 := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, checkerboardScalarIsometry_one, map_one]

/-- The isometries realizing two scalars compose to the isometry realizing their product. -/
theorem typeD4ScalarIsometry_mul (a b : Fˣ) :
    typeD4ScalarIsometry ht hF hω (a * b) =
      typeD4ScalarIsometry ht hF hω a * typeD4ScalarIsometry ht hF hω b := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, checkerboardScalarIsometry_mul, map_mul,
    ← typeD4ScalarIsometry_eq_conjMulEquiv, ← typeD4ScalarIsometry_eq_conjMulEquiv]

/-- The isometry realizing the inverse of a scalar is the inverse self-isometry. -/
@[simp]
theorem typeD4ScalarIsometry_inv (a : Fˣ) :
    typeD4ScalarIsometry ht hF hω a⁻¹ = (typeD4ScalarIsometry ht hF hω a)⁻¹ := by
  rw [typeD4ScalarIsometry_eq_conjMulEquiv, checkerboardScalarIsometry_inv, map_inv,
    ← typeD4ScalarIsometry_eq_conjMulEquiv]

end DynkinType

end TauCeti
