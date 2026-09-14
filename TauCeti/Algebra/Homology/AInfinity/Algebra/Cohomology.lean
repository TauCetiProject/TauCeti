/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Homology.AInfinity.Algebra

/-!
# The cohomology algebra of an A-infinity algebra

For an uncurved `A∞` algebra, the unary operation `m₁` is a differential and the binary operation
`m₂` descends to an associative multiplication on its cohomology.  On the chain level `m₂` need
not be associative: the arity-three Stasheff identity says that its associator on cycles is the
boundary of `-m₃`.  This file packages that standard construction as a nonunital `R`-algebra.

The signs in the Leibniz rule are expressed by `InternalGrading.koszulTwist`.  This gives identities
for arbitrary, rather than only homogeneous, inputs and keeps the proofs of closure under `m₂`
and absorption by boundaries independent of chosen homogeneous decompositions.

## Main definitions

* `AInfinityAlgebra.differential`: the unary operation `m₁` as a linear map.
* `AInfinityAlgebra.cycles`: the kernel of `m₁`, with multiplication induced by `m₂`.
* `AInfinityAlgebra.boundaries`: the image of `m₁` in the cycles, which absorbs multiplication
  on both sides.
* `AInfinityAlgebra.Cohomology`: cycles modulo boundaries, with its associative nonunital
  `R`-algebra structure.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 2, item “`A∞` algebras, categories,
morphisms, functors, modules, and bimodules”.  It supplies the cohomology algebra needed to state
the requested cohomologically unital variant without selecting a strict chain-level unit.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The differential underlying an uncurved `A∞` algebra. -/
def differential (𝒜 : AInfinityAlgebra R A) : A →ₗ[R] A :=
  (𝒜.m 1).curryRight ![]

@[simp]
theorem differential_apply (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x = 𝒜.m 1 ![x] := by
  simp [differential]

/-- The `A∞` differential is homogeneous of degree one. -/
theorem differential_isHomogeneous (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.differential 𝒜.grading.piece 𝒜.grading.piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  have h := (𝒜.m_degree 1 (by omega)).map_mem (fun _ ↦ p) ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  simpa [differential] using h

/-- The differential squares to zero. -/
@[simp]
theorem differential_sq (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential (𝒜.differential x) = 0 := by
  simpa using 𝒜.stasheff_arity_one x

/-- The graded Leibniz identity on arbitrary inputs.  The Koszul twist packages the sign which,
on a homogeneous left input `x` of degree `p`, is `(-1)^p`. -/
theorem differential_m_two (𝒜 : AInfinityAlgebra R A) (x y : A) :
    𝒜.differential (𝒜.m 2 ![x, y]) =
      𝒜.m 2 ![𝒜.differential x, y] +
        𝒜.m 2 ![𝒜.grading.koszulTwist 1 x, 𝒜.differential y] := by
  let L : MultilinearMap R (fun _ : Fin 2 ↦ A) A :=
    𝒜.differential.compMultilinearMap (𝒜.m 2)
  let Q : MultilinearMap R (fun _ : Fin 2 ↦ A) A :=
    (𝒜.m 2).compLinearMap ![𝒜.differential, LinearMap.id] +
      (𝒜.m 2).compLinearMap ![𝒜.grading.koszulTwist 1, 𝒜.differential]
  have hLQ : L = Q := by
    apply 𝒜.grading.multilinearMap_ext
    intro d z hz
    have h := 𝒜.stasheff_arity_two (z 0) (z 1) (d 0) (hz 0)
    unfold L Q
    simp only [LinearMap.compMultilinearMap_apply, add_apply,
      MultilinearMap.compLinearMap_apply]
    rw [show (fun i ↦ (![𝒜.differential, LinearMap.id] i) (z i)) =
        ![𝒜.differential (z 0), z 1] by funext i; fin_cases i <;> rfl,
      show (fun i ↦ (![𝒜.grading.koszulTwist 1, 𝒜.differential] i) (z i)) =
        ![𝒜.grading.koszulTwist 1 (z 0), 𝒜.differential (z 1)] by
          funext i; fin_cases i <;> rfl,
      𝒜.grading.koszulTwist_apply_of_mem (hz 0) 1, one_mul,
      ← negOnePowCast_eq_intCast]
    rw [show 𝒜.m 2 ![negOnePowCast R (d 0) • z 0, 𝒜.differential (z 1)] =
        negOnePowCast R (d 0) • 𝒜.m 2 ![z 0, 𝒜.differential (z 1)] by
      change ((𝒜.m 2).curryLeft (negOnePowCast R (d 0) • z 0))
        ![𝒜.differential (z 1)] = _
      rw [map_smul]
      rfl]
    rw [show z = ![z 0, z 1] by funext i; fin_cases i <;> rfl]
    simpa [differential] using h
  have h := DFunLike.congr_fun hLQ ![x, y]
  unfold L Q at h
  simp only [LinearMap.compMultilinearMap_apply, add_apply,
    MultilinearMap.compLinearMap_apply] at h
  convert h using 1
  · congr 2 <;> funext i <;> fin_cases i <;> rfl

/-- The cycles of an `A∞` algebra: the kernel of `m₁`. -/
def cycles (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.ker 𝒜.differential

@[simp]
theorem mem_cycles (𝒜 : AInfinityAlgebra R A) {x : A} :
    x ∈ 𝒜.cycles ↔ 𝒜.differential x = 0 := Iff.rfl

/-- Every differential is a cycle. -/
theorem differential_mem_cycles (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.differential x ∈ 𝒜.cycles :=
  𝒜.differential_sq x

/-- The binary operation takes cycles to cycles. -/
theorem m_two_mem_cycles (𝒜 : AInfinityAlgebra R A) {x y : A}
    (hx : x ∈ 𝒜.cycles) (hy : y ∈ 𝒜.cycles) :
    𝒜.m 2 ![x, y] ∈ 𝒜.cycles := by
  rw [𝒜.mem_cycles] at hx hy ⊢
  rw [𝒜.differential_m_two, hx, hy]
  rw [show 𝒜.m 2 ![0, y] = 0 by
      change ((𝒜.m 2).curryLeft 0) ![y] = 0
      rw [map_zero]
      rfl,
    show 𝒜.m 2 ![𝒜.grading.koszulTwist 1 x, 0] = 0 by
      simpa using map_zero ((𝒜.m 2).curryRight ![𝒜.grading.koszulTwist 1 x]), add_zero]

/-- Multiplication of cycles, induced by `m₂`. -/
def cyclesMul (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) : 𝒜.cycles :=
  ⟨𝒜.m 2 ![(x : A), (y : A)], 𝒜.m_two_mem_cycles x.2 y.2⟩

instance instMulCycles (𝒜 : AInfinityAlgebra R A) : Mul 𝒜.cycles :=
  ⟨𝒜.cyclesMul⟩

@[simp]
theorem coe_cycles_mul (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) :
    ((x * y : 𝒜.cycles) : A) = 𝒜.m 2 ![(x : A), (y : A)] := by
  change ((𝒜.cyclesMul x y : 𝒜.cycles) : A) = _
  rfl

/-- The differential with codomain restricted to cycles. -/
def boundaryMap (𝒜 : AInfinityAlgebra R A) : A →ₗ[R] 𝒜.cycles where
  toFun x := ⟨𝒜.differential x, 𝒜.differential_mem_cycles x⟩
  map_add' _ _ := Subtype.ext (map_add 𝒜.differential _ _)
  map_smul' _ _ := Subtype.ext (map_smul 𝒜.differential _ _)

@[simp]
theorem coe_boundaryMap (𝒜 : AInfinityAlgebra R A) (x : A) :
    (𝒜.boundaryMap x : A) = 𝒜.differential x := by
  simp [boundaryMap]

/-- The image of the differential, as a submodule of the cycles. -/
def boundaries (𝒜 : AInfinityAlgebra R A) : Submodule R 𝒜.cycles :=
  LinearMap.range 𝒜.boundaryMap

@[simp]
theorem mem_boundaries (𝒜 : AInfinityAlgebra R A) {z : 𝒜.cycles} :
    z ∈ 𝒜.boundaries ↔ ∃ x : A, 𝒜.differential x = z := by
  rw [boundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congr_arg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The cycle represented by a differential is a boundary. -/
theorem differential_mem_boundaries (𝒜 : AInfinityAlgebra R A) (x : A) :
    (⟨𝒜.differential x, 𝒜.differential_mem_cycles x⟩ : 𝒜.cycles) ∈ 𝒜.boundaries :=
  𝒜.mem_boundaries.mpr ⟨x, rfl⟩

/-- Left multiplication by a cycle, as a linear endomorphism of the cycles. -/
def cyclesLeftMul (𝒜 : AInfinityAlgebra R A) (x : 𝒜.cycles) :
    𝒜.cycles →ₗ[R] 𝒜.cycles where
  toFun y := 𝒜.cyclesMul x y
  map_add' y z := by
    apply Subtype.ext
    simpa [cyclesMul] using
      map_add ((𝒜.m 2).curryRight ![(x : A)]) (y : A) (z : A)
  map_smul' r y := by
    apply Subtype.ext
    dsimp [cyclesMul, instMulCycles]
    have h := map_smul ((𝒜.m 2).curryRight ![(x : A)]) r (y : A)
    simp only [MultilinearMap.curryRight_apply] at h
    rw [show Fin.snoc ![(x : A)] (r • (y : A)) = ![(x : A), r • (y : A)] by
        funext i; fin_cases i <;> rfl,
      show Fin.snoc ![(x : A)] (y : A) = ![(x : A), (y : A)] by
        funext i; fin_cases i <;> rfl] at h
    exact h

@[simp]
theorem cyclesLeftMul_apply (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) :
    𝒜.cyclesLeftMul x y = x * y := by
  change 𝒜.cyclesMul x y = (instMulCycles 𝒜).mul x y
  rfl

/-- Right multiplication by a cycle, as a linear endomorphism of the cycles. -/
def cyclesRightMul (𝒜 : AInfinityAlgebra R A) (y : 𝒜.cycles) :
    𝒜.cycles →ₗ[R] 𝒜.cycles where
  toFun x := 𝒜.cyclesMul x y
  map_add' x z := by
    apply Subtype.ext
    change ((𝒜.m 2).curryLeft ((x : A) + z)) ![(y : A)] =
      ((𝒜.m 2).curryLeft x) ![(y : A)] + ((𝒜.m 2).curryLeft z) ![(y : A)]
    exact DFunLike.congr_fun (map_add (𝒜.m 2).curryLeft (x : A) (z : A)) ![(y : A)]
  map_smul' r x := by
    apply Subtype.ext
    change ((𝒜.m 2).curryLeft (r • (x : A))) ![(y : A)] =
      r • ((𝒜.m 2).curryLeft x) ![(y : A)]
    exact DFunLike.congr_fun (map_smul (𝒜.m 2).curryLeft r (x : A)) ![(y : A)]

@[simp]
theorem cyclesRightMul_apply (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) :
    𝒜.cyclesRightMul y x = x * y := by
  change 𝒜.cyclesMul x y = (instMulCycles 𝒜).mul x y
  rfl

/-- A cycle times a boundary is a boundary. -/
theorem mul_mem_boundaries_left (𝒜 : AInfinityAlgebra R A) (x : 𝒜.cycles)
    {y : 𝒜.cycles} (hy : y ∈ 𝒜.boundaries) : x * y ∈ 𝒜.boundaries := by
  obtain ⟨b, hb⟩ := 𝒜.mem_boundaries.mp hy
  refine 𝒜.mem_boundaries.mpr ⟨𝒜.m 2 ![𝒜.grading.koszulTwist 1 (x : A), b], ?_⟩
  have hx : 𝒜.differential (x : A) = 0 := x.2
  have htwist : 𝒜.differential (𝒜.grading.koszulTwist 1 (x : A)) = 0 := by
    have h := LinearMap.congr_fun (𝒜.differential_isHomogeneous.koszulTwist_comp 1) (x : A)
    simp only [LinearMap.comp_apply, hx, map_zero, one_mul, Int.negOnePow_one,
      Units.val_neg, Units.val_one, LinearMap.smul_apply] at h
    have h' : -𝒜.differential (𝒜.grading.koszulTwist 1 (x : A)) = 0 := by
      simpa using h.symm
    exact neg_eq_zero.mp h'
  have hinvol : 𝒜.grading.koszulTwist 1 (𝒜.grading.koszulTwist 1 (x : A)) = x := by
    rw [← LinearMap.comp_apply, 𝒜.grading.koszulTwist_comp_self]
    rfl
  rw [𝒜.differential_m_two, htwist, hinvol, hb]
  rw [show 𝒜.m 2 ![0, b] = 0 by
    change ((𝒜.m 2).curryLeft 0) ![b] = 0
    rw [map_zero]
    rfl, zero_add]
  rfl

/-- A boundary times a cycle is a boundary. -/
theorem mul_mem_boundaries_right (𝒜 : AInfinityAlgebra R A) {x : 𝒜.cycles}
    (hx : x ∈ 𝒜.boundaries) (y : 𝒜.cycles) : x * y ∈ 𝒜.boundaries := by
  obtain ⟨a, ha⟩ := 𝒜.mem_boundaries.mp hx
  refine 𝒜.mem_boundaries.mpr ⟨𝒜.m 2 ![a, (y : A)], ?_⟩
  rw [𝒜.differential_m_two, show 𝒜.differential (y : A) = 0 from y.2, ha]
  rw [show 𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, 0] = 0 by
    simpa using map_zero ((𝒜.m 2).curryRight ![𝒜.grading.koszulTwist 1 a]), add_zero]
  rfl

/-- The degree-`p` cycles of an `A∞` algebra. -/
def cyclesDeg (𝒜 : AInfinityAlgebra R A) (p : ℤ) : Submodule R 𝒜.cycles :=
  (𝒜.grading.piece p).comap 𝒜.cycles.subtype

@[simp]
theorem mem_cyclesDeg (𝒜 : AInfinityAlgebra R A) {p : ℤ} {x : 𝒜.cycles} :
    x ∈ 𝒜.cyclesDeg p ↔ (x : A) ∈ 𝒜.grading.piece p := Iff.rfl

private theorem differential_decompose (𝒜 : AInfinityAlgebra R A) (p : ℤ) (x : A) :
    𝒜.differential (DirectSum.decompose 𝒜.grading.piece x p : A) =
      (DirectSum.decompose 𝒜.grading.piece (𝒜.differential x) (p + 1) : A) :=
  DirectSum.map_decompose_shift 𝒜.grading.piece 𝒜.grading.piece 𝒜.differential
    (· + 1) (add_left_injective 1)
    (fun _ _ hx ↦ 𝒜.differential_isHomogeneous.map_mem hx) p x

/-- The cycles inherit the internal grading of the `A∞` algebra. -/
noncomputable def cyclesGrading (𝒜 : AInfinityAlgebra R A) : InternalGrading R 𝒜.cycles := by
  letI : DirectSum.Decomposition 𝒜.cyclesDeg :=
    DirectSum.Decomposition.restrict 𝒜.grading.piece 𝒜.cyclesDeg 𝒜.cycles.subtype
      Subtype.val_injective (fun _ _ ↦ Iff.rfl) fun p x ↦ by
        refine ⟨⟨(DirectSum.decompose 𝒜.grading.piece (x : A) p : A), ?_⟩, rfl⟩
        rw [𝒜.mem_cycles, 𝒜.differential_decompose, show 𝒜.differential (x : A) = 0 from x.2]
        simp
  exact InternalGrading.ofDecomposition 𝒜.cyclesDeg

@[simp]
theorem cyclesGrading_piece (𝒜 : AInfinityAlgebra R A) (p : ℤ) :
    𝒜.cyclesGrading.piece p = 𝒜.cyclesDeg p := by
  simp [cyclesGrading]

/-- The cohomology of an `A∞` algebra: cycles modulo boundaries. -/
abbrev Cohomology (𝒜 : AInfinityAlgebra R A) := 𝒜.cycles ⧸ 𝒜.boundaries

/-- The quotient map from cycles to cohomology. -/
abbrev quotientMk (𝒜 : AInfinityAlgebra R A) : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
  Submodule.mkQ 𝒜.boundaries

@[simp]
theorem quotientMk_apply (𝒜 : AInfinityAlgebra R A) (x : 𝒜.cycles) :
    𝒜.quotientMk x = Submodule.Quotient.mk x := rfl

/-- A cycle represents zero in cohomology exactly when it is a boundary. -/
theorem quotientMk_eq_zero_iff (𝒜 : AInfinityAlgebra R A) {x : 𝒜.cycles} :
    𝒜.quotientMk x = 0 ↔ x ∈ 𝒜.boundaries := by
  exact Submodule.Quotient.mk_eq_zero 𝒜.boundaries

/-- The cohomology class of a differential vanishes. -/
@[simp]
theorem quotientMk_differential_eq_zero (𝒜 : AInfinityAlgebra R A) (x : A) :
    𝒜.quotientMk ⟨𝒜.differential x, 𝒜.differential_mem_cycles x⟩ = 0 :=
  𝒜.quotientMk_eq_zero_iff.mpr (𝒜.differential_mem_boundaries x)

/-- Every cohomology class has a cycle representative. -/
theorem quotientMk_surjective (𝒜 : AInfinityAlgebra R A) :
    Function.Surjective 𝒜.quotientMk :=
  Submodule.Quotient.mk_surjective 𝒜.boundaries

/-- Multiplication of cycles respects equivalence modulo boundaries in both variables. -/
theorem cyclesMul_respects_boundaries (𝒜 : AInfinityAlgebra R A)
    {x₁ x₂ y₁ y₂ : 𝒜.cycles} (hx : 𝒜.boundaries.quotientRel x₁ x₂)
    (hy : 𝒜.boundaries.quotientRel y₁ y₂) :
    𝒜.boundaries.quotientRel (𝒜.cyclesMul x₁ y₁) (𝒜.cyclesMul x₂ y₂) := by
  change 𝒜.boundaries.quotientRel (x₁ * y₁) (x₂ * y₂)
  rw [Submodule.quotientRel_def] at hx hy ⊢
  have h₁ := 𝒜.mul_mem_boundaries_right hx y₁
  have h₂ := 𝒜.mul_mem_boundaries_left x₂ hy
  have hrewrite : x₁ * y₁ - x₂ * y₂ = (x₁ - x₂) * y₁ + x₂ * (y₁ - y₂) := by
    calc
      x₁ * y₁ - x₂ * y₂ = (x₁ * y₁ - x₂ * y₁) + (x₂ * y₁ - x₂ * y₂) := by abel
      _ = (x₁ - x₂) * y₁ + x₂ * (y₁ - y₂) := by
        congr 1
        · exact ((𝒜.cyclesRightMul y₁).map_sub x₁ x₂).symm
        · exact ((𝒜.cyclesLeftMul x₂).map_sub y₁ y₂).symm
  rw [hrewrite]
  exact 𝒜.boundaries.add_mem h₁ h₂

/-- Multiplication on cohomology representatives, well-defined modulo boundaries. -/
def cohomologyMul (𝒜 : AInfinityAlgebra R A) : 𝒜.Cohomology → 𝒜.Cohomology → 𝒜.Cohomology :=
  Quotient.map₂ 𝒜.cyclesMul fun _ _ hx _ _ hy ↦
    cyclesMul_respects_boundaries 𝒜 hx hy

private theorem quotient_mul_assoc (𝒜 : AInfinityAlgebra R A) (x y z : 𝒜.cycles) :
    𝒜.quotientMk ((x * y) * z) = 𝒜.quotientMk (x * (y * z)) := by
  let L : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
    𝒜.quotientMk.comp ((𝒜.cyclesRightMul z).comp (𝒜.cyclesRightMul y))
  let Q : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
    𝒜.quotientMk.comp (𝒜.cyclesRightMul (y * z))
  suffices L x = Q x by simpa [L, Q]
  apply LinearMap.congr_fun (𝒜.cyclesGrading.linearMap_ext fun p a ha ↦ ?_)
  let L' : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
    𝒜.quotientMk.comp ((𝒜.cyclesRightMul z).comp (𝒜.cyclesLeftMul a))
  let Q' : 𝒜.cycles →ₗ[R] 𝒜.Cohomology :=
    𝒜.quotientMk.comp ((𝒜.cyclesLeftMul a).comp (𝒜.cyclesRightMul z))
  suffices L' y = Q' y by simpa [L, Q, L', Q'] using this
  apply LinearMap.congr_fun (𝒜.cyclesGrading.linearMap_ext fun q b hb ↦ ?_)
  rw [cyclesGrading_piece, mem_cyclesDeg] at ha hb
  apply (Submodule.Quotient.eq 𝒜.boundaries).mpr
  apply 𝒜.mem_boundaries.mpr
  refine ⟨-𝒜.m 3 ![(a : A), (b : A), (z : A)], ?_⟩
  have h := 𝒜.stasheff_arity_three (a : A) (b : A) (z : A) p q ha hb
  have ha0 : 𝒜.m 1 ![(a : A)] = 0 := by rw [← 𝒜.differential_apply]; exact a.2
  have hb0 : 𝒜.m 1 ![(b : A)] = 0 := by rw [← 𝒜.differential_apply]; exact b.2
  have hz0 : 𝒜.m 1 ![(z : A)] = 0 := by rw [← 𝒜.differential_apply]; exact z.2
  rw [ha0, hb0, hz0] at h
  have hm30 : 𝒜.m 3 ![0, (b : A), (z : A)] = 0 := by
    exact (𝒜.m 3).map_coord_zero 0 rfl
  have hm31 : 𝒜.m 3 ![(a : A), 0, (z : A)] = 0 := by
    exact (𝒜.m 3).map_coord_zero 1 rfl
  have hm32 : 𝒜.m 3 ![(a : A), (b : A), 0] = 0 := by
    exact (𝒜.m 3).map_coord_zero 2 rfl
  rw [hm30, hm31, hm32, smul_zero, add_zero] at h
  change 𝒜.differential (-𝒜.m 3 ![(a : A), (b : A), (z : A)]) =
    (𝒜.m 2 ![𝒜.m 2 ![(a : A), (b : A)], (z : A)] -
      𝒜.m 2 ![(a : A), 𝒜.m 2 ![(b : A), (z : A)]])
  rw [map_neg, differential_apply]
  simp only [add_zero, smul_zero] at h
  apply neg_eq_of_add_eq_zero_right
  simpa only [sub_eq_add_neg, add_assoc] using h

/-- The additive and multiplicative operations on cohomology form a nonassociative nonunital
ring before the arity-three identity is used to prove associativity. -/
instance instNonUnitalNonAssocRingCohomology (𝒜 : AInfinityAlgebra R A) :
    NonUnitalNonAssocRing 𝒜.Cohomology := by
  letI : Mul 𝒜.Cohomology := ⟨𝒜.cohomologyMul⟩
  exact NonUnitalNonAssocRing.mk
    (fun x y z ↦ by
      refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
      refine Submodule.Quotient.induction_on 𝒜.boundaries y fun b ↦ ?_
      refine Submodule.Quotient.induction_on 𝒜.boundaries z fun c ↦ ?_
      change 𝒜.quotientMk (𝒜.cyclesMul a (b + c)) =
        𝒜.quotientMk (𝒜.cyclesMul a b) + 𝒜.quotientMk (𝒜.cyclesMul a c)
      exact congr_arg 𝒜.quotientMk ((𝒜.cyclesLeftMul a).map_add b c))
    (fun x y z ↦ by
      refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
      refine Submodule.Quotient.induction_on 𝒜.boundaries y fun b ↦ ?_
      refine Submodule.Quotient.induction_on 𝒜.boundaries z fun c ↦ ?_
      change 𝒜.quotientMk (𝒜.cyclesMul (a + b) c) =
        𝒜.quotientMk (𝒜.cyclesMul a c) + 𝒜.quotientMk (𝒜.cyclesMul b c)
      exact congr_arg 𝒜.quotientMk ((𝒜.cyclesRightMul c).map_add a b))
    (fun x ↦ by
      refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
      change 𝒜.quotientMk (𝒜.cyclesMul 0 a) = 𝒜.quotientMk 0
      exact congr_arg 𝒜.quotientMk ((𝒜.cyclesRightMul a).map_zero))
    (fun x ↦ by
      refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
      change 𝒜.quotientMk (𝒜.cyclesMul a 0) = 𝒜.quotientMk 0
      exact congr_arg 𝒜.quotientMk ((𝒜.cyclesLeftMul a).map_zero))

@[simp]
theorem quotientMk_mul (𝒜 : AInfinityAlgebra R A) (x y : 𝒜.cycles) :
    𝒜.quotientMk (x * y) = 𝒜.quotientMk x * 𝒜.quotientMk y := by
  change Submodule.Quotient.mk (𝒜.cyclesMul x y) =
    𝒜.cohomologyMul (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
  rfl

/-- Cohomology multiplication is associative: the arity-three Stasheff identity makes every
chain-level associator a boundary. -/
instance instNonUnitalRingCohomology (𝒜 : AInfinityAlgebra R A) : NonUnitalRing 𝒜.Cohomology :=
  NonUnitalRing.mk fun x y z ↦ by
    refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
    refine Submodule.Quotient.induction_on 𝒜.boundaries y fun b ↦ ?_
    refine Submodule.Quotient.induction_on 𝒜.boundaries z fun c ↦ ?_
    change (𝒜.quotientMk a * 𝒜.quotientMk b) * 𝒜.quotientMk c =
      𝒜.quotientMk a * (𝒜.quotientMk b * 𝒜.quotientMk c)
    rw [← 𝒜.quotientMk_mul, ← 𝒜.quotientMk_mul,
      ← 𝒜.quotientMk_mul, ← 𝒜.quotientMk_mul]
    exact 𝒜.quotient_mul_assoc a b c

instance (𝒜 : AInfinityAlgebra R A) : IsScalarTower R 𝒜.Cohomology 𝒜.Cohomology where
  smul_assoc r x y := by
    refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
    refine Submodule.Quotient.induction_on 𝒜.boundaries y fun b ↦ ?_
    change (r • 𝒜.quotientMk a) * 𝒜.quotientMk b =
      r • (𝒜.quotientMk a * 𝒜.quotientMk b)
    rw [← map_smul 𝒜.quotientMk, ← 𝒜.quotientMk_mul,
      ← 𝒜.quotientMk_mul, ← map_smul 𝒜.quotientMk]
    exact congr_arg 𝒜.quotientMk ((𝒜.cyclesRightMul b).map_smul r a)

instance (𝒜 : AInfinityAlgebra R A) : SMulCommClass R 𝒜.Cohomology 𝒜.Cohomology where
  smul_comm r x y := by
    refine Submodule.Quotient.induction_on 𝒜.boundaries x fun a ↦ ?_
    refine Submodule.Quotient.induction_on 𝒜.boundaries y fun b ↦ ?_
    change r • (𝒜.quotientMk a * 𝒜.quotientMk b) =
      𝒜.quotientMk a * (r • 𝒜.quotientMk b)
    rw [← map_smul 𝒜.quotientMk, ← 𝒜.quotientMk_mul,
      ← 𝒜.quotientMk_mul, ← map_smul 𝒜.quotientMk]
    exact congr_arg 𝒜.quotientMk ((𝒜.cyclesLeftMul a).map_smul r b).symm

end AInfinityAlgebra

end TauCeti
