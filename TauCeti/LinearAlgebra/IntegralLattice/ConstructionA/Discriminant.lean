/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Basic
public import Mathlib.Algebra.Field.ZMod

import TauCeti.LinearAlgebra.IntegralLattice.Index
import TauCeti.LinearAlgebra.IntegralLattice.Scaling
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

private def reduction : (ι → ℤ) →+ (ι → ZMod m) :=
  ((Int.castAddHom (ZMod m)).toIntLinearMap.compLeft ι).toAddMonoidHom

private def rationalCast : (ι → ℤ) →+ (ι → ℚ) :=
  ((Int.castAddHom ℚ).toIntLinearMap.compLeft ι).toAddMonoidHom

private theorem rationalCast_injective : Function.Injective (rationalCast (ι := ι)) :=
  Function.Injective.piMap fun _ ↦ Int.cast_injective

private theorem lattice_toAddSubgroup (C : AddSubgroup (ι → ZMod m)) :
    (lattice m C).toAddSubgroup =
      (C.comap (reduction m)).map (rationalCast (ι := ι)) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_lattice]
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_comap]
  have hreduction (z : ι → ℤ) : reduction m z = fun i ↦ (z i : ZMod m) := by
    funext i
    simp [reduction, LinearMap.compLeft]
  have hrationalCast (z : ι → ℤ) : rationalCast z = fun i ↦ (z i : ℚ) := by
    funext i
    simp [rationalCast, LinearMap.compLeft]
  constructor <;> rintro ⟨z, hz, hzx⟩ <;>
    exact ⟨z, by simpa only [hreduction] using hz,
      by simpa only [hrationalCast] using hzx⟩

/-- The relative index of the zero-code Construction A carrier in the carrier attached to `C` is
the number of codewords of `C`. -/
theorem relIndex_lattice_bot (C : AddSubgroup (ι → ZMod m)) :
    (lattice m (⊥ : AddSubgroup (ι → ZMod m))).toAddSubgroup.relIndex
      (lattice m C).toAddSubgroup = Nat.card C := by
  rw [lattice_toAddSubgroup, lattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ rationalCast_injective]
  have hker : (⊥ : AddSubgroup (ι → ZMod m)).comap (reduction m) = (reduction m).ker := by
    ext
    simp
  rw [hker, AddSubgroup.relIndex_ker]
  have hmap : (C.comap (reduction m)).map (reduction m) = C := by
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      obtain ⟨z, rfl⟩ := (Function.Surjective.piMap fun _ ↦ ZMod.intCast_surjective) x
      exact ⟨z, hx, rfl⟩
  rw [hmap]

variable [Fintype ι]

private noncomputable def scaleEquiv : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ) :=
  LinearEquiv.piCongrRight fun _ ↦
    LinearEquiv.smulOfUnit (M := ℚ) (Units.mk0 (m : ℚ) (NeZero.ne _))

omit [Fintype ι] in
@[simp]
private theorem scaleEquiv_apply (x : ι → ℚ) (i : ι) : scaleEquiv m x i = m * x i :=
  rfl

private theorem map_standardLattice_carrier :
    let _ := Classical.decEq ι
    (IntegralLattice.ofGramMatrix (Pi.basisFun ℚ ι) (1 : Matrix ι ι ℤ)
        Matrix.isSymm_one).carrier.map
        ((scaleEquiv m).restrictScalars ℤ).toLinearMap =
      lattice m (⊥ : AddSubgroup (ι → ZMod m)) := by
  classical
  ext x
  rw [Submodule.mem_map_equiv,
    IntegralLattice.mem_ofGramMatrix_basisFun_carrier_iff, mem_lattice]
  constructor
  · intro hx
    choose z hz using hx
    refine ⟨fun i ↦ m * z i, ?_, ?_⟩
    · ext i
      simp
    · have hzx : (fun i ↦ (z i : ℚ)) = (scaleEquiv m).symm x := funext hz
      calc
        (fun i ↦ ((m * z i : ℤ) : ℚ)) = scaleEquiv m (fun i ↦ (z i : ℚ)) := by
          funext i
          simp
        _ = x := by rw [hzx, LinearEquiv.apply_symm_apply]
  · rintro ⟨z, hz, rfl⟩
    have hzero : (fun i ↦ (z i : ZMod m)) = 0 := by simpa using hz
    have hdiv (i : ι) : (m : ℤ) ∣ z i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrFun hzero i
    choose w hw using hdiv
    have hcast : (fun i ↦ (z i : ℚ)) = scaleEquiv m (fun i ↦ (w i : ℚ)) := by
      funext i
      have hwi : z i = m * w i := by simpa [mul_comm] using hw i
      rw [hwi]
      simp
    have hsymm : ((scaleEquiv m).restrictScalars ℤ).symm (fun i ↦ (z i : ℚ)) =
        (scaleEquiv m).symm (fun i ↦ (z i : ℚ)) := by
      apply (scaleEquiv m).injective
      rw [LinearEquiv.apply_symm_apply]
      change ((scaleEquiv m).restrictScalars ℤ)
          (((scaleEquiv m).restrictScalars ℤ).symm (fun i ↦ (z i : ℚ))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [hsymm, hcast, LinearEquiv.symm_apply_apply]
    exact fun i ↦ ⟨w i, rfl⟩

private noncomputable def scaledStandardIsometry :
    let _ := Classical.decEq ι
    IntegralLattice.Isometry
      ((m : ℤ) • IntegralLattice.ofGramMatrix (Pi.basisFun ℚ ι)
        (1 : Matrix ι ι ℤ) Matrix.isSymm_one)
      (integralLattice m (⊥ : AddSubgroup (ι → ZMod m)) (by simp)) where
  toIsometryEquiv :=
    { toLinearEquiv := scaleEquiv m
      map_app' := by
        intro x y
        have hx : (scaleEquiv m).toFun x = fun i ↦ m * x i :=
          funext (scaleEquiv_apply m x)
        have hy : (scaleEquiv m).toFun y = fun i ↦ m * y i :=
          funext (scaleEquiv_apply m y)
        rw [hx, hy]
        rw [integralLattice_form, form_apply, IntegralLattice.smul_form]
        simp only [LinearMap.smul_apply, Int.cast_natCast]
        simp [Matrix.one_apply, dotProduct]
        field_simp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_carrier := by
    rw [IntegralLattice.smul_carrier, integralLattice_carrier]
    exact map_standardLattice_carrier m

/-- The zero-code Construction A lattice has diagonal Gram matrix `m I`, hence discriminant
`m ^ #ι`. -/
@[simp]
theorem discriminant_integralLattice_bot :
    (integralLattice m (⊥ : AddSubgroup (ι → ZMod m))
      (by simp)).discriminant = (m : ℕ) ^ Fintype.card ι := by
  classical
  rw [← (scaledStandardIsometry m).discriminant_eq, IntegralLattice.discriminant_smul,
    IntegralLattice.finrank_carrier, Module.finrank_fintype_fun_eq_card]
  rw [IntegralLattice.discriminant_ofGramMatrix, Matrix.det_one]
  simp

/-- **The discriminant formula for Construction A, with its divisibility visible:** the
discriminant times the square of the number of codewords is `m ^ #ι`. -/
theorem discriminant_mul_natCard_sq (C : AddSubgroup (ι → ZMod m))
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
  rw [relIndex_lattice_bot] at hdisc
  rw [← discriminant_integralLattice_bot m]
  exact hdisc.symm

/-- The square of the number of codewords divides `m ^ #ι`, as required for the Construction A
discriminant quotient. -/
theorem natCard_sq_dvd_modulus_pow_card (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    Nat.card C ^ 2 ∣ (m : ℕ) ^ Fintype.card ι :=
  ⟨(integralLattice m C hC).discriminant, by
    simpa [mul_comm] using (discriminant_mul_natCard_sq m C hC).symm⟩

/-- The discriminant of an integral Construction A lattice is the exact natural-number quotient
`m ^ #ι / (#C)^2`. -/
theorem discriminant_integralLattice (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).discriminant =
      (m : ℕ) ^ Fintype.card ι / Nat.card C ^ 2 := by
  apply Nat.eq_div_of_mul_eq_right
  · exact pow_ne_zero 2 (Nat.card_pos.ne')
  · simpa [mul_comm] using discriminant_mul_natCard_sq m C hC

/-- For a self-orthogonal linear code of dimension `k` over the prime field `ZMod p`, the
Construction A discriminant is `p ^ (n - 2k)`. -/
theorem discriminant_integralLattice_of_prime {p : ℕ} [hp : Fact p.Prime]
    (C : Submodule (ZMod p) (ι → ZMod p)) (hC : C ≤ C.euclideanDual) :
    (integralLattice ⟨p, hp.out.pos⟩ C.toAddSubgroup hC).discriminant =
      p ^ (Fintype.card ι - 2 * Module.finrank (ZMod p) C) := by
  have hdim := Submodule.two_mul_finrank_le_card_of_le_euclideanDual
    (K := ZMod p) (ι := ι) (C := C) hC
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (2 * Module.finrank (ZMod p) C))
  have hdisc := discriminant_mul_natCard_sq ⟨p, hp.out.pos⟩ C.toAddSubgroup hC
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
