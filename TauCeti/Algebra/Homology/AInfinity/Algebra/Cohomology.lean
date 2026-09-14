/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Homology.AInfinity.Algebra

/-!
# Cohomology of an `A∞` algebra

The unary operation of an `A∞` algebra squares to zero, so it has cycles, boundaries, and a total
cohomology module.  The arity-two Stasheff identity is the graded Leibniz rule for the binary
operation, which therefore descends to a bilinear product on cohomology.

The Leibniz sign depends only on the degree of the left factor.  With a cycle on the right it
disappears, so a boundary times a cycle is a boundary.  With a cycle on the left it is removed by
the degree-one Koszul twist, which carries cycles to cycles, so a cycle times a boundary is a
boundary as well.  Neither argument needs homogeneous inputs.

## Main definitions

* `TauCeti.AInfinityAlgebra.differential`: the unary operation as a linear endomorphism.
* `TauCeti.AInfinityAlgebra.mul`: the binary operation as a bilinear map.
* `TauCeti.AInfinityAlgebra.cycles` and `TauCeti.AInfinityAlgebra.boundaries`: the cycles and
  boundaries of the unary operation.
* `TauCeti.AInfinityAlgebra.Cohomology`: the total cohomology module.
* `TauCeti.AInfinityAlgebra.cohomologyClassLinearMap`: the quotient map from cycles to cohomology.
* `TauCeti.AInfinityAlgebra.cohomologyClass`: the class represented by a cycle.
* `TauCeti.AInfinityAlgebra.cohomologyMul`: the product on cohomology induced by the binary
  operation.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Cycles and boundaries -/

/-- The unary `A∞` operation, regarded as a linear differential on the total module. -/
def differential (𝒜 : AInfinityAlgebra R A) : A →ₗ[R] A :=
  (𝒜.m 1).curryRight ![]

/-- Evaluating the differential is evaluating the unary operation. -/
@[simp]
theorem differential_apply (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x = 𝒜.m 1 ![x] := by
  simp [differential, MultilinearMap.curryRight_apply]

/-- The unary operation squares to zero. -/
@[simp]
theorem differential_comp_self_eq_zero (𝒜 : AInfinityAlgebra R A) :
    𝒜.differential ∘ₗ 𝒜.differential = 0 := by
  ext x
  simp only [LinearMap.comp_apply, differential_apply, LinearMap.zero_apply,
    𝒜.stasheff_arity_one]

/-- The cycles of an `A∞` algebra are the kernel of its unary operation. -/
def cycles (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.ker 𝒜.differential

/-- An element is a cycle exactly when its unary operation vanishes. -/
@[simp]
theorem mem_cycles (𝒜 : AInfinityAlgebra R A) {x : A} :
    x ∈ 𝒜.cycles ↔ 𝒜.m 1 ![x] = 0 := by
  rw [cycles, LinearMap.mem_ker, differential_apply]

/-- The boundaries of an `A∞` algebra are the range of its unary operation. -/
def boundaries (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.range 𝒜.differential

/-- An element is a boundary exactly when it is the unary operation of some element. -/
@[simp]
theorem mem_boundaries (𝒜 : AInfinityAlgebra R A) {x : A} :
    x ∈ 𝒜.boundaries ↔ ∃ y : A, 𝒜.m 1 ![y] = x := by
  simp only [boundaries, LinearMap.mem_range, differential_apply]

/-- Every boundary is a cycle. -/
theorem boundaries_le_cycles (𝒜 : AInfinityAlgebra R A) : 𝒜.boundaries ≤ 𝒜.cycles := by
  rintro _ ⟨y, rfl⟩
  rw [mem_cycles, differential_apply]
  exact 𝒜.stasheff_arity_one y

/-- The differential of every element is a boundary. -/
theorem differential_mem_boundaries (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x ∈ 𝒜.boundaries :=
  ⟨x, rfl⟩

/-- The differential of every element is a cycle. -/
theorem differential_mem_cycles (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x ∈ 𝒜.cycles :=
  𝒜.boundaries_le_cycles (𝒜.differential_mem_boundaries x)

/-! ### The binary operation on cycles and boundaries -/

/-- The binary `A∞` operation, regarded as a bilinear map on the total module. -/
def mul (𝒜 : AInfinityAlgebra R A) : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (fun x y ↦ 𝒜.m 2 ![x, y])
    (fun x x' y ↦ by
      convert (𝒜.m 2).map_update_add ![x, y] 0 x x' using 3 <;> ext i <;> fin_cases i <;> rfl)
    (fun c x y ↦ by
      convert (𝒜.m 2).map_update_smul ![x, y] 0 c x using 3 <;> ext i <;> fin_cases i <;> rfl)
    (fun x y y' ↦ by
      convert (𝒜.m 2).map_update_add ![x, y] 1 y y' using 3 <;> ext i <;> fin_cases i <;> rfl)
    (fun c x y ↦ by
      convert (𝒜.m 2).map_update_smul ![x, y] 1 c y using 3 <;> ext i <;> fin_cases i <;> rfl)

/-- Evaluating the bilinear product is evaluating the binary operation. -/
@[simp]
theorem mul_apply (𝒜 : AInfinityAlgebra R A) (x y : A) : 𝒜.mul x y = 𝒜.m 2 ![x, y] := by
  simp [mul]

/-- The unary operation anticommutes with the degree-one Koszul twist. -/
theorem m_one_koszulTwist (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.m 1 ![𝒜.grading.koszulTwist 1 x] = -𝒜.grading.koszulTwist 1 (𝒜.m 1 ![x]) := by
  have h : 𝒜.differential ∘ₗ 𝒜.grading.koszulTwist 1 =
      -(𝒜.grading.koszulTwist 1 ∘ₗ 𝒜.differential) := by
    refine 𝒜.grading.linearMap_ext fun p y hy ↦ ?_
    have hdy : 𝒜.differential y ∈ 𝒜.grading.piece (p + 1) := by
      simpa using (𝒜.m_degree 1 one_pos).map_mem (fun _ ↦ p) ![y] (fun _ ↦ by simpa using hy)
    rw [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      𝒜.grading.koszulTwist_apply_of_mem hy, map_smul, 𝒜.grading.koszulTwist_apply_of_mem hdy,
      ← neg_smul]
    congr 1
    simp [Int.negOnePow_succ]
  simpa using LinearMap.congr_fun h x

/-- The graded Leibniz rule for arbitrary inputs, with the sign on the second term carried by the
degree-one Koszul twist of the left factor. -/
theorem m_one_m_two (𝒜 : AInfinityAlgebra R A) (x y : A) :
    𝒜.m 1 ![𝒜.m 2 ![x, y]] =
      𝒜.m 2 ![𝒜.m 1 ![x], y] + 𝒜.m 2 ![𝒜.grading.koszulTwist 1 x, 𝒜.m 1 ![y]] := by
  have h : 𝒜.differential ∘ₗ 𝒜.mul.flip y =
      𝒜.mul.flip y ∘ₗ 𝒜.differential +
        𝒜.mul.flip (𝒜.m 1 ![y]) ∘ₗ 𝒜.grading.koszulTwist 1 := by
    refine 𝒜.grading.linearMap_ext fun p z hz ↦ ?_
    simpa [𝒜.grading.koszulTwist_apply_of_mem hz, negOnePowCast_eq_intCast] using
      𝒜.stasheff_arity_two z y p hz
  simpa using LinearMap.congr_fun h x

/-- The binary operation of two cycles is a cycle. -/
theorem m_two_mem_cycles (𝒜 : AInfinityAlgebra R A) {x y : A} (hx : x ∈ 𝒜.cycles)
    (hy : y ∈ 𝒜.cycles) : 𝒜.m 2 ![x, y] ∈ 𝒜.cycles := by
  rw [mem_cycles] at hx hy ⊢
  rw [𝒜.m_one_m_two, hx, hy, ← mul_apply, ← mul_apply]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

/-- The binary operation of a boundary and a cycle is a boundary. -/
theorem m_two_mem_boundaries_of_left (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.boundaries) (hy : y ∈ 𝒜.cycles) : 𝒜.m 2 ![x, y] ∈ 𝒜.boundaries := by
  obtain ⟨z, rfl⟩ := hx
  rw [mem_cycles] at hy
  refine ⟨𝒜.m 2 ![z, y], ?_⟩
  rw [differential_apply, differential_apply, 𝒜.m_one_m_two, hy, ← 𝒜.mul_apply _ 0]
  simp only [map_zero, add_zero]

/-- The binary operation of a cycle and a boundary is a boundary. -/
theorem m_two_mem_boundaries_of_right (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.boundaries) : 𝒜.m 2 ![x, y] ∈ 𝒜.boundaries := by
  obtain ⟨z, rfl⟩ := hy
  rw [mem_cycles] at hx
  refine ⟨𝒜.m 2 ![𝒜.grading.koszulTwist 1 x, z], ?_⟩
  have htwist : 𝒜.grading.koszulTwist 1 (𝒜.grading.koszulTwist 1 x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (𝒜.grading.koszulTwist_comp_self 1) x
  rw [differential_apply, differential_apply, 𝒜.m_one_m_two, 𝒜.m_one_koszulTwist, hx, htwist,
    map_zero, neg_zero, ← 𝒜.mul_apply 0]
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-! ### Cohomology -/

/-- The boundaries, viewed as a submodule of the cycles. -/
def boundariesInCycles (𝒜 : AInfinityAlgebra R A) : Submodule R 𝒜.cycles :=
  𝒜.boundaries.submoduleOf 𝒜.cycles

/-- A cycle belongs to `boundariesInCycles` exactly when its underlying element is a boundary. -/
@[simp]
theorem mem_boundariesInCycles (𝒜 : AInfinityAlgebra R A) {x : 𝒜.cycles} :
    x ∈ 𝒜.boundariesInCycles ↔ (x : A) ∈ 𝒜.boundaries := by
  rw [boundariesInCycles, Submodule.submoduleOf, Submodule.mem_comap]
  rfl

/-- The total cohomology module of an `A∞` algebra: unary cycles modulo unary boundaries.

Its elements are not required to be homogeneous; degree conditions on representatives are stated
separately using `AInfinityAlgebra.grading`. -/
abbrev Cohomology (𝒜 : AInfinityAlgebra R A) := 𝒜.cycles ⧸ 𝒜.boundariesInCycles

/-- The linear quotient map from cycles to cohomology. -/
def cohomologyClassLinearMap (𝒜 : AInfinityAlgebra R A) : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
  𝒜.boundariesInCycles.mkQ

/-- The cohomology class represented by a cycle. -/
def cohomologyClass (𝒜 : AInfinityAlgebra R A) {x : A} (hx : x ∈ 𝒜.cycles) : 𝒜.Cohomology :=
  𝒜.cohomologyClassLinearMap ⟨x, hx⟩

/-- Every cohomology class is represented by a cycle. -/
theorem exists_cohomologyClass_eq (𝒜 : AInfinityAlgebra R A) (c : 𝒜.Cohomology) :
    ∃ (x : A) (hx : x ∈ 𝒜.cycles), 𝒜.cohomologyClass hx = c := by
  induction c using Submodule.Quotient.induction_on with
  | H x => exact ⟨x, x.2, rfl⟩

/-- Two cycles represent the same cohomology class exactly when their difference is a boundary. -/
@[simp]
theorem cohomologyClass_eq_iff (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) :
    𝒜.cohomologyClass hx = 𝒜.cohomologyClass hy ↔ x - y ∈ 𝒜.boundaries := by
  simp only [cohomologyClass, cohomologyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, mem_boundariesInCycles]
  rfl

/-- A cycle represents zero in cohomology exactly when it is a boundary. -/
@[simp]
theorem cohomologyClass_eq_zero_iff (𝒜 : AInfinityAlgebra R A) {x : A}
    (hx : x ∈ 𝒜.cycles) : 𝒜.cohomologyClass hx = 0 ↔ x ∈ 𝒜.boundaries := by
  simp only [cohomologyClass, cohomologyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, mem_boundariesInCycles]

/-- The cohomology class of a boundary is zero. -/
@[simp]
theorem cohomologyClass_m_one_eq_zero (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.cohomologyClass (𝒜.mem_cycles.mpr (𝒜.stasheff_arity_one x)) = 0 :=
  (𝒜.cohomologyClass_eq_zero_iff _).mpr (𝒜.mem_boundaries.mpr ⟨x, rfl⟩)

/-- The binary operation, restricted to a bilinear map on cycles. -/
def cyclesMul (𝒜 : AInfinityAlgebra R A) : 𝒜.cycles →ₗ[R] 𝒜.cycles →ₗ[R] 𝒜.cycles :=
  LinearMap.mk₂ R (fun x y ↦ ⟨𝒜.m 2 ![x, y], 𝒜.m_two_mem_cycles x.2 y.2⟩)
    (fun x x' y ↦ Subtype.ext <| by
      simpa only [mul_apply, Submodule.coe_add] using 𝒜.mul.map_add₂ x x' y)
    (fun c x y ↦ Subtype.ext <| by
      simpa only [mul_apply, Submodule.coe_smul] using 𝒜.mul.map_smul₂ c x y)
    (fun x y y' ↦ Subtype.ext <| by
      simpa only [mul_apply, Submodule.coe_add] using (𝒜.mul x).map_add y y')
    (fun c x y ↦ Subtype.ext <| by
      simpa only [mul_apply, Submodule.coe_smul] using (𝒜.mul x).map_smul c y)

/-- The underlying element of the product of two cycles is their binary operation. -/
@[simp]
theorem coe_cyclesMul (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) :
    (𝒜.cyclesMul x y : A) = 𝒜.m 2 ![x, y] := by
  simp [cyclesMul]

/-- The product on cohomology induced by the binary operation. -/
def cohomologyMul (𝒜 : AInfinityAlgebra R A) :
    𝒜.Cohomology →ₗ[R] 𝒜.Cohomology →ₗ[R] 𝒜.Cohomology :=
  (𝒜.cyclesMul.compr₂ 𝒜.boundariesInCycles.mkQ).liftQ₂ _ _
    (fun _ hx ↦ LinearMap.ext fun y ↦ (Submodule.Quotient.mk_eq_zero _).mpr <|
      (𝒜.mem_boundariesInCycles).mpr <|
        𝒜.m_two_mem_boundaries_of_left ((𝒜.mem_boundariesInCycles).mp hx) y.2)
    (fun _ hy ↦ LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).mpr <|
      (𝒜.mem_boundariesInCycles).mpr <|
        𝒜.m_two_mem_boundaries_of_right x.2 ((𝒜.mem_boundariesInCycles).mp hy))

/-- The product of two classes is represented by the binary operation of their representatives. -/
@[simp]
theorem cohomologyMul_cohomologyClass (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) :
    𝒜.cohomologyMul (𝒜.cohomologyClass hx) (𝒜.cohomologyClass hy) =
      𝒜.cohomologyClass (𝒜.m_two_mem_cycles hx hy) := by
  simp only [cohomologyMul, cohomologyClass]
  rfl

end AInfinityAlgebra

end TauCeti
