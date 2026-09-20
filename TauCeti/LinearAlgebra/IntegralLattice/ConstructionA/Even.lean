/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Discriminant
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Even

/-!
# Evenness of Construction A lattices

The norm of a Construction A vector is the dot product of any integer lift divided by the
modulus, so the lattice `P_m(C)` is even exactly when `2m` divides `∑ i, zᵢ²` for every integer
lift `z` of a codeword. That divisibility is precisely the vanishing of the quadratic value

```text
q_m(c) = (∑ i, lift (cᵢ)²) / (2m)  mod ℤ
```

of the standard coordinate discriminant module over `ℤ/m`, which exists when `m` is even. So
for even `m` the Construction A lattice of `C` is even exactly when `C` is a quadratically
isotropic subgroup of that module. For odd `m` and a nonempty coordinate type the lattice is
never even, because it always contains a coordinate vector of norm `m`.

At `m = 2` the quadratic value is a quarter of the Hamming weight, so evenness of the lattice is
divisibility of all codeword weights by four; for a doubly-even Euclidean self-dual binary code
the unimodularity criterion and the positive definiteness of the normalized dot product then say
that the lattice is definite, even, and unimodular.

## References

* W. Ebeling, *Lattices and Codes*, §1.3, Proposition 1.3, for the binary criteria.
* A. Munemasa and H. Tamura, *The codes and the lattices of Hadamard matrices*, §4, for the
  general `ℤ/m` normalization.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 7, §§2, 6,
  for Construction A and its Type II form.
-/

public section

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ+) {ι : Type*} [Fintype ι]

/-- **A Construction A lattice is even exactly when `2m` divides the sum of the squares of every
integer lift of a codeword.** -/
theorem isEven_integralLattice_iff_intCast (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).IsEven ↔
      ∀ z : ι → ℤ, (fun i ↦ ((z i : ZMod m))) ∈ C → (2 * m : ℤ) ∣ ∑ i, z i ^ 2 := by
  have hm0 : ((m : ℕ) : ℚ) ≠ 0 := NeZero.ne _
  rw [IntegralLattice.isEven_iff_forall_norm]
  constructor
  · intro h z hz
    have hmem : (fun i ↦ ((z i : ℚ))) ∈ (integralLattice m C hC).carrier := by
      rw [integralLattice_carrier]
      exact (intCast_mem_lattice m z).mpr hz
    obtain ⟨k, hk⟩ := h ⟨_, hmem⟩
    rw [integralLattice_norm_intCast, div_eq_iff hm0] at hk
    refine ⟨k, ?_⟩
    have : ((∑ i, z i ^ 2 : ℤ) : ℚ) = ((2 * m * k : ℤ) : ℚ) := by push_cast [hk]; ring
    exact_mod_cast this
  · intro h x
    obtain ⟨z, hz, hzx⟩ :=
      (mem_lattice m).mp (by rw [← integralLattice_carrier m C hC]; exact x.2)
    obtain ⟨k, hk⟩ := h z hz
    refine ⟨k, ?_⟩
    rw [← hzx, integralLattice_norm_intCast, hk]
    push_cast
    field_simp

/-- **Over an even modulus, a Construction A lattice is even exactly when its code is
quadratically isotropic** in the standard coordinate discriminant module over `ℤ/m`. -/
theorem isEven_integralLattice_iff_isIsotropic (hm : Even (m : ℕ))
    (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).IsEven ↔
      ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).IsIsotropic C := by
  rw [isEven_integralLattice_iff_intCast,
    isIsotropic_coordinatePower_zmodStandard_quadratic_intCast_iff]

/-- Over an even modulus, a Construction A lattice is even exactly when `2m` divides the sum of
the squares of the canonical representatives of every codeword. -/
theorem isEven_integralLattice_iff (hm : Even (m : ℕ)) (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).IsEven ↔ ∀ x ∈ C, 2 * (m : ℕ) ∣ ∑ i, (x i).val ^ 2 := by
  rw [isEven_integralLattice_iff_isIsotropic m hm,
    isIsotropic_coordinatePower_zmodStandard_quadratic_iff]

/-- Over an odd modulus a Construction A lattice is never even: the coordinate vector `m eᵢ`
has norm `m`. -/
theorem not_isEven_integralLattice_of_odd (hm : Odd (m : ℕ)) [Nonempty ι]
    (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    ¬ (integralLattice m C hC).IsEven := by
  classical
  have hm0 : (m : ℚ) ≠ 0 := NeZero.ne _
  rw [IntegralLattice.isEven_iff_forall_norm]
  intro h
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hmem : Pi.single i (m : ℚ) ∈ (integralLattice m C hC).carrier := by
    rw [integralLattice_carrier]
    exact single_mem_lattice m C i
  obtain ⟨k, hk⟩ := h ⟨_, hmem⟩
  simp only [integralLattice_norm, dotProduct_single, Pi.single_eq_same, mul_div_assoc,
    div_self hm0, mul_one] at hk
  rw [Nat.odd_iff] at hm
  have hdvd : (2 : ℕ) ∣ (m : ℕ) := by
    have h2 : (2 : ℤ) ∣ ((m : ℕ) : ℤ) := ⟨k, by exact_mod_cast hk⟩
    exact_mod_cast h2
  omega

/-! ## The binary case -/

/-- A Construction A lattice at modulus two is even exactly when every codeword weight is
divisible by four. -/
theorem isEven_integralLattice_two_iff (C : AddSubgroup (ι → ZMod 2))
    (hC : AddSubgroup.toZModSubmodule 2 C ≤ (AddSubgroup.toZModSubmodule 2 C).euclideanDual) :
    (integralLattice 2 C hC).IsEven ↔ ∀ x ∈ C, 4 ∣ hammingNorm x :=
  (isEven_integralLattice_iff_isIsotropic 2 even_two C hC).trans
    (isIsotropic_coordinatePower_zmodStandard_two_iff C)

/-- A Construction A lattice at modulus two is even exactly when its binary linear code is
doubly even. -/
theorem isEven_integralLattice_two_iff_isDoublyEven (C : LinearCode (ZMod 2) ι)
    (hC : AddSubgroup.toZModSubmodule 2 C.toAddSubgroup ≤
      (AddSubgroup.toZModSubmodule 2 C.toAddSubgroup).euclideanDual) :
    (integralLattice 2 C.toAddSubgroup hC).IsEven ↔ BinaryCode.IsDoublyEven C := by
  rw [BinaryCode.isDoublyEven_iff]
  refine (isEven_integralLattice_two_iff C.toAddSubgroup hC).trans ?_
  simp only [Submodule.mem_toAddSubgroup]

end TauCeti.ConstructionA
