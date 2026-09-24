/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Cohomology of an `A∞` algebra

The unary operation of an `A∞` algebra squares to zero, so it has cycles, boundaries, and a total
cohomology module.  The arity-two Stasheff identity is the graded Leibniz rule for the binary
operation, which therefore descends to a bilinear product on cohomology.

The Leibniz sign depends only on the degree of the left factor.  With a cycle on the right it
disappears, so a boundary times a cycle is a boundary.  With a cycle on the left it is removed by
the degree-one Koszul twist, which carries cycles to cycles, so a cycle times a boundary is a
boundary as well.  Neither argument needs homogeneous inputs.

The arbitrary-input arity-three identity `AInfinityAlgebra.m_one_m_three` exhibits the associator
of the binary operation as a unary boundary, so the induced product is associative on cohomology.
Together with bilinearity, this makes the cohomology an associative nonunital `R`-algebra.

The unary operation has degree one, so it commutes with the homogeneous projections up to a shift
of the degree by one.  Hence the homogeneous components of a cycle are cycles, and the degree-`p`
component of a boundary `m₁(y)` is the boundary `m₁(y_{p-1})`.  The cycles therefore inherit the
internal grading, the boundaries form a homogeneous submodule of them, and the cohomology is
graded by the classes of homogeneous cycles.  The binary operation has degree zero, so the
cohomology is a graded nonunital algebra: the graded algebra `H(A)` which carries the minimal
models of `A` and against which formality of `A` is measured.

## Main definitions

* `TauCeti.AInfinityAlgebra.cycles` and `TauCeti.AInfinityAlgebra.boundaries`: the cycles and
  boundaries of the unary operation.
* `TauCeti.AInfinityAlgebra.Cohomology`: the total cohomology module.
* `TauCeti.AInfinityAlgebra.cohomologyClassLinearMap`: the quotient map from cycles to cohomology.
* `TauCeti.AInfinityAlgebra.cohomologyClass`: the class represented by a cycle.
* `TauCeti.AInfinityAlgebra.cohomologyMul`: the product on cohomology induced by the binary
  operation.
* `TauCeti.AInfinityAlgebra.instNonUnitalRingCohomology`, together with the scalar tower and
  commuting-scalars instances: the cohomology as an associative nonunital `R`-algebra.
* `TauCeti.AInfinityAlgebra.cyclesGrading`: the internal grading of the cycles.
* `TauCeti.AInfinityAlgebra.cohomologyGrading`: the internal grading of the cohomology by the
  classes of homogeneous cycles.

## Main results

* `TauCeti.AInfinityAlgebra.isHomogeneous_cycles`: the homogeneous components of a cycle are
  cycles.
* `TauCeti.AInfinityAlgebra.decompose_cohomologyClass`: the degree-`p` component of the class of a
  cycle is the class of its degree-`p` component.
* `TauCeti.AInfinityAlgebra.instGradedMulCohomologyGrading`: the product on cohomology has degree
  zero.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Cycles and boundaries -/

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

Its elements are not required to be homogeneous; its internal grading is
`AInfinityAlgebra.cohomologyGrading`. -/
abbrev Cohomology (𝒜 : AInfinityAlgebra R A) := 𝒜.cycles ⧸ 𝒜.boundariesInCycles

/-- The linear quotient map from cycles to cohomology. -/
def cohomologyClassLinearMap (𝒜 : AInfinityAlgebra R A) : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
  𝒜.boundariesInCycles.mkQ

/-- The cohomology class represented by a cycle. -/
def cohomologyClass (𝒜 : AInfinityAlgebra R A) {x : A} (hx : x ∈ 𝒜.cycles) : 𝒜.Cohomology :=
  𝒜.cohomologyClassLinearMap ⟨x, hx⟩

/-- A cohomology class is the quotient class of its cycle representative.  This is the bridge
through which maps out of cohomology are built by the universal property of the quotient. -/
theorem cohomologyClass_eq_mk (𝒜 : AInfinityAlgebra R A) {x : A} (hx : x ∈ 𝒜.cycles) :
    𝒜.cohomologyClass hx = Submodule.Quotient.mk ⟨x, hx⟩ := (rfl)

/-- Zero represents zero in cohomology. -/
@[simp]
theorem cohomologyClass_zero (𝒜 : AInfinityAlgebra R A) :
    𝒜.cohomologyClass (𝒜.cycles.zero_mem) = 0 := by
  exact 𝒜.cohomologyClassLinearMap.map_zero

/-- The class of a sum of cycles is the sum of their classes. -/
@[simp]
theorem cohomologyClass_add (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) :
    𝒜.cohomologyClass (𝒜.cycles.add_mem hx hy) =
      𝒜.cohomologyClass hx + 𝒜.cohomologyClass hy := by
  exact 𝒜.cohomologyClassLinearMap.map_add ⟨x, hx⟩ ⟨y, hy⟩

/-- The class of a scalar multiple of a cycle is the scalar multiple of its class. -/
@[simp]
theorem cohomologyClass_smul (𝒜 : AInfinityAlgebra R A) (r : R) {x : A}
    (hx : x ∈ 𝒜.cycles) :
    𝒜.cohomologyClass (𝒜.cycles.smul_mem r hx) = r • 𝒜.cohomologyClass hx := by
  exact 𝒜.cohomologyClassLinearMap.map_smul r ⟨x, hx⟩

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

private theorem m_two_assoc_sub_mem_boundaries (𝒜 : AInfinityAlgebra R A) {x y z : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) (hz : z ∈ 𝒜.cycles) :
    𝒜.m 2 ![𝒜.m 2 ![x, y], z] - 𝒜.m 2 ![x, 𝒜.m 2 ![y, z]] ∈ 𝒜.boundaries := by
  -- On cycles the three correction terms of `m_one_m_three` have a vanishing input, so the
  -- associator is the unary boundary of `-m₃`.
  rw [mem_cycles] at hx hy hz
  have h₀ : 𝒜.m 3 ![(0 : A), y, z] = 0 := (𝒜.m 3).map_coord_zero 0 rfl
  have h₁ : 𝒜.m 3 ![𝒜.grading.koszulTwist 1 x, 0, z] = 0 :=
    (𝒜.m 3).map_coord_zero 1 rfl
  have h₂ : 𝒜.m 3 ![𝒜.grading.koszulTwist 1 x, 𝒜.grading.koszulTwist 1 y, 0] = 0 :=
    (𝒜.m 3).map_coord_zero 2 rfl
  rw [mem_boundaries]
  refine ⟨-𝒜.m 3 ![x, y, z], ?_⟩
  rw [← differential_apply, map_neg, differential_apply, 𝒜.m_one_m_three, hx, hy, hz,
    h₀, h₁, h₂]
  abel

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

/-- The product induced on cohomology is associative. -/
theorem cohomologyMul_assoc (𝒜 : AInfinityAlgebra R A) (a b c : 𝒜.Cohomology) :
    𝒜.cohomologyMul (𝒜.cohomologyMul a b) c =
      𝒜.cohomologyMul a (𝒜.cohomologyMul b c) := by
  obtain ⟨x, hx, rfl⟩ := 𝒜.exists_cohomologyClass_eq a
  obtain ⟨y, hy, rfl⟩ := 𝒜.exists_cohomologyClass_eq b
  obtain ⟨z, hz, rfl⟩ := 𝒜.exists_cohomologyClass_eq c
  simp only [cohomologyMul_cohomologyClass]
  rw [cohomologyClass_eq_iff]
  exact 𝒜.m_two_assoc_sub_mem_boundaries hx hy hz

/-! ### The cohomology algebra -/

/-- The cohomology of an `A∞` algebra is an associative nonunital ring under `cohomologyMul`. -/
instance instNonUnitalRingCohomology (𝒜 : AInfinityAlgebra R A) :
    NonUnitalRing 𝒜.Cohomology where
  mul := fun a b ↦ 𝒜.cohomologyMul a b
  left_distrib a b c := (𝒜.cohomologyMul a).map_add b c
  right_distrib a b c := LinearMap.map_add₂ 𝒜.cohomologyMul a b c
  zero_mul a := LinearMap.map_zero₂ 𝒜.cohomologyMul a
  mul_zero a := (𝒜.cohomologyMul a).map_zero
  mul_assoc := 𝒜.cohomologyMul_assoc

/-- Multiplication on cohomology is `cohomologyMul`. -/
@[simp]
theorem cohomology_mul_eq_cohomologyMul (𝒜 : AInfinityAlgebra R A) (a b : 𝒜.Cohomology) :
    a * b = 𝒜.cohomologyMul a b :=
  rfl

instance (𝒜 : AInfinityAlgebra R A) : IsScalarTower R 𝒜.Cohomology 𝒜.Cohomology where
  smul_assoc r a b := LinearMap.map_smul₂ 𝒜.cohomologyMul r a b

instance (𝒜 : AInfinityAlgebra R A) : SMulCommClass R 𝒜.Cohomology 𝒜.Cohomology where
  smul_comm r a b := ((𝒜.cohomologyMul a).map_smul r b).symm

/-! ### The grading of cycles and cohomology -/

section Grading

open _root_.DirectSum

/-- The unary operation commutes with the homogeneous projections, up to the degree shift by
one. -/
@[simp]
theorem differential_decompose (𝒜 : AInfinityAlgebra R A) (p : ℤ) (x : A) :
    𝒜.differential (decompose 𝒜.grading.piece x p : A) =
      (decompose 𝒜.grading.piece (𝒜.differential x) (p + 1) : A) :=
  DirectSum.map_decompose_shift 𝒜.grading.piece 𝒜.grading.piece 𝒜.differential (· + 1)
    (add_left_injective 1) (fun _ _ ↦ 𝒜.differential_mem_piece) p x

/-- The cycles form a homogeneous submodule: the homogeneous components of a cycle are cycles. -/
theorem isHomogeneous_cycles (𝒜 : AInfinityAlgebra R A) :
    SetLike.IsHomogeneous 𝒜.grading.piece 𝒜.cycles := by
  intro p x hx
  rw [cycles, LinearMap.mem_ker] at hx ⊢
  rw [differential_decompose, hx]
  simp

/-- The internal grading of the cycles by homogeneous cycles. -/
noncomputable def cyclesGrading (𝒜 : AInfinityAlgebra R A) : InternalGrading R 𝒜.cycles :=
  𝒜.grading.submodule 𝒜.cycles 𝒜.isHomogeneous_cycles

/-- A cycle has degree `p` exactly when its underlying element does. -/
@[simp]
theorem mem_cyclesGrading_piece (𝒜 : AInfinityAlgebra R A) {p : ℤ} {x : 𝒜.cycles} :
    x ∈ 𝒜.cyclesGrading.piece p ↔ (x : A) ∈ 𝒜.grading.piece p :=
  𝒜.grading.mem_submodule_piece 𝒜.cycles 𝒜.isHomogeneous_cycles

/-- Homogeneous projection of cycles is homogeneous projection in the ambient module. -/
@[simp]
theorem coe_decompose_cyclesGrading (𝒜 : AInfinityAlgebra R A) (p : ℤ) (x : 𝒜.cycles) :
    ((decompose 𝒜.cyclesGrading.piece x p : 𝒜.cycles) : A) =
      decompose 𝒜.grading.piece (x : A) p :=
  𝒜.grading.coe_decompose_submodule 𝒜.cycles 𝒜.isHomogeneous_cycles p x

/-- The boundaries form a homogeneous submodule of the cycles: the degree-`p` component of the
boundary `m₁(y)` is the boundary `m₁(y_{p-1})`. -/
theorem isHomogeneous_boundariesInCycles (𝒜 : AInfinityAlgebra R A) :
    SetLike.IsHomogeneous 𝒜.cyclesGrading.piece 𝒜.boundariesInCycles := by
  intro p x hx
  rw [mem_boundariesInCycles] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  rw [coe_decompose_cyclesGrading, ← hy, ← sub_add_cancel p 1, ← differential_decompose]
  exact 𝒜.differential_mem_boundaries _

/-- The internal grading of the cohomology: its degree-`p` piece consists of the classes of
homogeneous cycles of degree `p`. -/
noncomputable def cohomologyGrading (𝒜 : AInfinityAlgebra R A) : InternalGrading R 𝒜.Cohomology :=
  𝒜.cyclesGrading.quotient 𝒜.boundariesInCycles 𝒜.isHomogeneous_boundariesInCycles

/-- A cohomology class has degree `p` exactly when it is represented by a cycle of degree `p`. -/
theorem mem_cohomologyGrading_piece_iff (𝒜 : AInfinityAlgebra R A) {p : ℤ}
    {c : 𝒜.Cohomology} :
    c ∈ 𝒜.cohomologyGrading.piece p ↔
      ∃ (x : A) (hx : x ∈ 𝒜.cycles), x ∈ 𝒜.grading.piece p ∧ 𝒜.cohomologyClass hx = c := by
  rw [cohomologyGrading, InternalGrading.mem_quotient_piece_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, 𝒜.mem_cyclesGrading_piece.1 hx, rfl⟩
  · rintro ⟨x, hx, hp, rfl⟩
    exact ⟨⟨x, hx⟩, 𝒜.mem_cyclesGrading_piece.2 hp, rfl⟩

/-- The class of a cycle of degree `p` has degree `p`. -/
theorem cohomologyClass_mem_cohomologyGrading_piece (𝒜 : AInfinityAlgebra R A) {p : ℤ} {x : A}
    (hx : x ∈ 𝒜.cycles) (hp : x ∈ 𝒜.grading.piece p) :
    𝒜.cohomologyClass hx ∈ 𝒜.cohomologyGrading.piece p :=
  𝒜.mem_cohomologyGrading_piece_iff.2 ⟨x, hx, hp, rfl⟩

/-- The degree-`p` component of the class of a cycle is the class of its degree-`p` component. -/
@[simp]
theorem decompose_cohomologyClass (𝒜 : AInfinityAlgebra R A) (p : ℤ) {x : A}
    (hx : x ∈ 𝒜.cycles) :
    (decompose 𝒜.cohomologyGrading.piece (𝒜.cohomologyClass hx) p : 𝒜.Cohomology) =
      𝒜.cohomologyClass (𝒜.isHomogeneous_cycles p hx) := by
  rw [cohomologyClass_eq_mk, cohomologyGrading, InternalGrading.decompose_quotient_mk,
    cohomologyClass_eq_mk]
  exact congrArg _ (Subtype.ext (𝒜.coe_decompose_cyclesGrading p ⟨x, hx⟩))

/-- The product on cohomology has degree zero. -/
theorem cohomologyMul_mem_cohomologyGrading_piece (𝒜 : AInfinityAlgebra R A) {p q : ℤ}
    {a b : 𝒜.Cohomology} (ha : a ∈ 𝒜.cohomologyGrading.piece p)
    (hb : b ∈ 𝒜.cohomologyGrading.piece q) :
    𝒜.cohomologyMul a b ∈ 𝒜.cohomologyGrading.piece (p + q) := by
  obtain ⟨x, hx, hxp, rfl⟩ := 𝒜.mem_cohomologyGrading_piece_iff.1 ha
  obtain ⟨y, hy, hyq, rfl⟩ := 𝒜.mem_cohomologyGrading_piece_iff.1 hb
  rw [cohomologyMul_cohomologyClass]
  exact 𝒜.cohomologyClass_mem_cohomologyGrading_piece _ (by
    simpa only [mul_apply] using 𝒜.mul_mem_piece hxp hyq)

/-- The cohomology of an `A∞` algebra is a graded nonunital algebra. -/
instance instGradedMulCohomologyGrading (𝒜 : AInfinityAlgebra R A) :
    SetLike.GradedMul 𝒜.cohomologyGrading.piece where
  mul_mem _ _ _ _ ha hb := 𝒜.cohomologyMul_mem_cohomologyGrading_piece ha hb

end Grading

end AInfinityAlgebra

end TauCeti
