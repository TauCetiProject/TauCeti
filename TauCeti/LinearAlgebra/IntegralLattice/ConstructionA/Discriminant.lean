/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import Mathlib.Algebra.Field.ZMod

import TauCeti.LinearAlgebra.IntegralLattice.Index
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates

/-!
# The discriminant of a Construction A lattice

This file computes the index and discriminant of the rational Construction A lattice attached to
an additive code over `ZMod m`.  Reduction modulo `m` identifies the quotient of the carrier of a
code `C` by the zero-code carrier with `C` itself.  Thus adjoining the codewords enlarges the
zero-code lattice by index `#C`, while the zero-code lattice has diagonal Gram matrix `m I`.

Consequently, whenever `C` is self-orthogonal so that Construction A is integral,

```text
disc(P_m(C)) * (#C)^2 = m^(#ι).
```

The multiplicative form records the divisibility needed for the quotient formula and remains
valid without introducing truncated natural-number division.

## References

* W. Ebeling, *Lattices and Codes*, §1.3.
* A. Munemasa and H. Tamura, *The codes and the lattices of Hadamard matrices*, §4.
-/

public section

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ+) {ι : Type*}

private theorem lattice_toAddSubgroup (C : AddSubgroup (ι → ZMod m)) :
    (lattice m C).toAddSubgroup =
      (C.comap ((Int.castAddHom (ZMod m)).compLeft ι)).map ((Int.castAddHom ℚ).compLeft ι) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_lattice]
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_comap]
  constructor <;> rintro ⟨z, hz, hzx⟩ <;> exact ⟨z, hz, hzx⟩

/-- Construction A preserves relative indices: the relative index of the carrier of `C` in the
carrier of `D` is the relative index of `C` in `D`. -/
@[simp]
theorem relIndex_lattice (C D : AddSubgroup (ι → ZMod m)) :
    (lattice m C).toAddSubgroup.relIndex (lattice m D).toAddSubgroup = C.relIndex D := by
  have hinj : Function.Injective ((Int.castAddHom ℚ).compLeft ι) :=
    Function.Injective.piMap fun _ ↦ Int.cast_injective
  have hsurj : Function.Surjective ((Int.castAddHom (ZMod m)).compLeft ι) :=
    Function.Surjective.piMap fun _ ↦ ZMod.intCast_surjective
  rw [lattice_toAddSubgroup, lattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective hsurj]

variable [Fintype ι]

private theorem map_standardLattice_carrier [DecidableEq ι] :
    (IntegralLattice.ofGramMatrix (Pi.basisFun ℚ ι) (1 : Matrix ι ι ℤ)
          Matrix.isSymm_one).carrier.map
        ((LinearEquiv.smulOfNeZero ℚ (ι → ℚ) (m : ℚ)
          (NeZero.ne _)).restrictScalars ℤ).toLinearMap =
      lattice m (⊥ : AddSubgroup (ι → ZMod m)) := by
  classical
  have hm : ((m : ℕ) : ℚ) ≠ 0 := NeZero.ne _
  ext x
  rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
    IntegralLattice.mem_ofGramMatrix_basisFun_carrier_iff, mem_lattice]
  simp only [LinearEquiv.smulOfNeZero_symm_apply, Units.smul_def, Units.val_inv_eq_inv_val,
    Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro hx
    choose z hz using hx
    refine ⟨fun i ↦ (m : ℤ) * z i, by simp [funext_iff], ?_⟩
    funext i
    push_cast
    rw [hz i]
    field_simp
  · rintro ⟨w, hw, rfl⟩
    have hzero : (fun i ↦ (w i : ZMod m)) = 0 := by simpa using hw
    intro i
    obtain ⟨v, hv⟩ : (m : ℤ) ∣ w i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrFun hzero i
    refine ⟨v, ?_⟩
    simp only [hv]
    push_cast
    field_simp

/-- Multiplying every coordinate by `m` is an isometry from the standard coordinate lattice `ℤ^ι`,
with its dot product scaled by `m`, onto the Construction A lattice of the zero code.  It exhibits
the zero-code lattice as `m ℤ^ι` carrying the normalized form. -/
noncomputable def scaledStandardIsometry :=
  letI := Classical.decEq ι
  ({
    toIsometryEquiv :=
      { toLinearEquiv := LinearEquiv.smulOfNeZero ℚ (ι → ℚ) (m : ℚ) (NeZero.ne _)
        map_app' x y := by
          have hm : ((m : ℕ) : ℚ) ≠ 0 := NeZero.ne _
          have hrow (i : ι) : ∑ j, (((1 : Matrix ι ι ℤ) i j : ℤ) : ℚ) * y j = y i := by
            simp [Matrix.one_apply]
          rw [integralLattice_form, form_apply, IntegralLattice.smul_form,
            LinearMap.smul_apply, LinearMap.smul_apply,
            IntegralLattice.form_ofGramMatrix_basisFun_apply]
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            LinearEquiv.smulOfNeZero_apply, hrow, dotProduct, Pi.smul_apply, smul_eq_mul,
            Int.cast_natCast]
          rw [div_eq_iff hm, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by ring }
    map_carrier := by
      rw [IntegralLattice.smul_carrier, integralLattice_carrier]
      exact map_standardLattice_carrier (m := m)
  } : IntegralLattice.Isometry
    ((m : ℤ) • IntegralLattice.ofGramMatrix (Pi.basisFun ℚ ι)
      (1 : Matrix ι ι ℤ) Matrix.isSymm_one)
    (integralLattice m (⊥ : AddSubgroup (ι → ZMod m)) (by simp)))

/-- The scaled-standard isometry acts by multiplying every coordinate by `m`. -/
@[simp]
theorem scaledStandardIsometry_apply (x : ι → ℚ) :
    scaledStandardIsometry m x = (m : ℚ) • x := by
  rw [scaledStandardIsometry]
  rfl

/-- The zero-code Construction A lattice has diagonal Gram matrix `m I`, hence discriminant
`m ^ #ι`. -/
theorem integralLattice_discriminant_bot :
    (integralLattice m (⊥ : AddSubgroup (ι → ZMod m))
      (by simp)).discriminant = (m : ℕ) ^ Fintype.card ι := by
  classical
  rw [← (scaledStandardIsometry m).discriminant_eq, IntegralLattice.discriminant_smul,
    IntegralLattice.finrank_carrier, Module.finrank_fintype_fun_eq_card]
  rw [IntegralLattice.discriminant_ofGramMatrix, Matrix.det_one]
  simp

/-- **The discriminant formula for Construction A, with its divisibility visible:** the
discriminant times the square of the number of codewords is `m ^ #ι`. -/
theorem integralLattice_discriminant_mul_natCard_sq (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).discriminant * Nat.card C ^ 2 =
      (m : ℕ) ^ Fintype.card ι := by
  let L₀ := integralLattice m (⊥ : AddSubgroup (ι → ZMod m)) (by simp)
  have hform : L₀.form = (integralLattice m C hC).form := by
    rw [integralLattice_form, integralLattice_form]
  have hcarrier : L₀.carrier ≤ (integralLattice m C hC).carrier := by
    rw [integralLattice_carrier, integralLattice_carrier, lattice_le_lattice_iff]
    exact bot_le
  have hdisc := L₀.discriminant_eq_mul_relIndex_sq (integralLattice m C hC)
    hform hcarrier
  dsimp only [L₀] at hdisc
  rw [integralLattice_carrier, integralLattice_carrier] at hdisc
  rw [relIndex_lattice, AddSubgroup.relIndex_bot_left] at hdisc
  rw [← integralLattice_discriminant_bot m]
  exact hdisc.symm

/-- The square of the number of codewords divides `m ^ #ι`, as required for the Construction A
discriminant quotient. -/
theorem natCard_sq_dvd_modulus_pow_card (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    Nat.card C ^ 2 ∣ (m : ℕ) ^ Fintype.card ι :=
  ⟨(integralLattice m C hC).discriminant, by
    simpa [mul_comm] using (integralLattice_discriminant_mul_natCard_sq m C hC).symm⟩

/-- The discriminant of an integral Construction A lattice is the exact natural-number quotient
`m ^ #ι / (#C)^2`. -/
@[simp]
theorem integralLattice_discriminant (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).discriminant =
      (m : ℕ) ^ Fintype.card ι / Nat.card C ^ 2 := by
  apply Nat.eq_div_of_mul_eq_right
  · exact pow_ne_zero 2 (Nat.card_pos.ne')
  · simpa [mul_comm] using integralLattice_discriminant_mul_natCard_sq m C hC

/-- For a self-orthogonal linear code of dimension `k` over the prime field `ZMod p`, the
Construction A discriminant is `p ^ (n - 2k)`. -/
@[simp]
theorem integralLattice_discriminant_of_prime {p : ℕ} [hp : Fact p.Prime]
    (C : Submodule (ZMod p) (ι → ZMod p)) (hC : C ≤ C.euclideanDual) :
    (integralLattice ⟨p, hp.out.pos⟩ C.toAddSubgroup hC).discriminant =
      p ^ (Fintype.card ι - 2 * Module.finrank (ZMod p) C) := by
  have hdim := Submodule.two_mul_finrank_le_card_of_le_euclideanDual
    (K := ZMod p) (ι := ι) (C := C) hC
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (2 * Module.finrank (ZMod p) C))
  have hdisc := integralLattice_discriminant_mul_natCard_sq ⟨p, hp.out.pos⟩ C.toAddSubgroup hC
  calc
    (integralLattice ⟨p, hp.out.pos⟩ C.toAddSubgroup hC).discriminant *
          p ^ (2 * Module.finrank (ZMod p) C) =
        (integralLattice ⟨p, hp.out.pos⟩ C.toAddSubgroup hC).discriminant *
          Nat.card C ^ 2 := by
            rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := C), Nat.card_zmod, ← pow_mul]
            simp [mul_comm]
    _ = p ^ Fintype.card ι := hdisc
    _ = p ^ (Fintype.card ι - 2 * Module.finrank (ZMod p) C) *
        p ^ (2 * Module.finrank (ZMod p) C) := (pow_sub_mul_pow p hdim).symm

end TauCeti.ConstructionA
