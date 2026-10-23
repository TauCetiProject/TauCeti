/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction

/-!
# Construction B

For a binary linear code `C` with coordinates `ι`, Construction B is the sublattice of the
Construction A carrier `{x ∈ ℤ^ι : x mod 2 ∈ C}` cut out by the congruence `∑ xᵢ ≡ 0 (mod 4)`.
It carries the Construction A form, the dot product halved, and is an integral lattice whenever
`C` is self-orthogonal.

When `C` is even, every Construction A vector has an even coordinate sum, so half the coordinate
sum reduced modulo two is an additive character `ConstructionB.sumHalf` of the Construction A
carrier. Its kernel is the Construction B carrier, and it is surjective as soon as there is a
coordinate. Hence Construction B has index two in Construction A, and its discriminant is four
times the discriminant of Construction A.

When `C` is doubly even, write a Construction A vector as `c + 2z`, where `c` is the `0`/`1`
lift of its reduction modulo two. It lies in Construction B exactly when `∑ zᵢ` is even, because
the weight of `c` is divisible by four. Construction B then inherits evenness from
Construction A.

Applied to the extended binary Golay code, Construction B is the index-two sublattice of the
Golay Construction A lattice from which the Leech lattice is obtained by gluing in an odd shift.

## Main declarations

* `TauCeti.ConstructionB.lattice`: the Construction B carrier, characterized by `mem_lattice`
  and `intCast_mem_lattice`.
* `TauCeti.ConstructionB.val_add_two_mul_mem_lattice_iff`: the parity description of membership
  for doubly even codes.
* `TauCeti.ConstructionB.sumHalf`: half the coordinate sum modulo two, with kernel
  `ker_sumHalf` and surjectivity `sumHalf_surjective`.
* `TauCeti.ConstructionB.relIndex_lattice`: Construction B has index two in Construction A.
* `TauCeti.ConstructionB.integralLattice`: Construction B as an integral lattice, with
  `discriminant_integralLattice` and `isEven_integralLattice`.

## References

* J. Leech and N. J. A. Sloane, *Sphere packing and error-correcting codes*, Canadian Journal of
  Mathematics 23 (1971), reprinted as Chapter 5 of J. H. Conway and N. J. A. Sloane,
  *Sphere Packings, Lattices and Groups*.
-/

public section

namespace TauCeti.ConstructionB

open Matrix

variable {ι : Type*} [Fintype ι] (C : LinearCode (ZMod 2) ι)

/-- The rational carrier of Construction B: the Construction A vectors of the binary code `C`
whose coordinate sum is divisible by four. -/
def lattice : Submodule ℤ (ι → ℚ) where
  carrier := {x | x ∈ ConstructionA.lattice 2 C.toAddSubgroup ∧ ∃ k : ℤ, ∑ i, x i = 4 * k}
  add_mem' := by
    rintro x y ⟨hx, k, hk⟩ ⟨hy, l, hl⟩
    refine ⟨add_mem hx hy, k + l, ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, hk, hl]
    push_cast
    ring
  zero_mem' := ⟨zero_mem _, 0, by simp⟩
  smul_mem' := by
    rintro n x ⟨hx, k, hk⟩
    refine ⟨Submodule.smul_mem _ n hx, n * k, ?_⟩
    simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum, hk]
    push_cast
    ring

variable {C}

/-- Membership in Construction B: a Construction A vector whose coordinate sum is divisible by
four. -/
theorem mem_lattice {x : ι → ℚ} :
    x ∈ lattice C ↔ x ∈ ConstructionA.lattice 2 C.toAddSubgroup ∧ ∃ k : ℤ, ∑ i, x i = 4 * k :=
  Iff.rfl

variable (C)

/-- Construction B lies inside Construction A. -/
theorem lattice_le : lattice C ≤ ConstructionA.lattice 2 C.toAddSubgroup :=
  fun _ hx ↦ hx.1

/-- An integer vector lies in Construction B exactly when it reduces to a codeword modulo two and
its coordinate sum is divisible by four. -/
@[simp]
theorem intCast_mem_lattice (z : ι → ℤ) :
    (fun i ↦ (z i : ℚ)) ∈ lattice C ↔ (fun i ↦ (z i : ZMod 2)) ∈ C ∧ 4 ∣ ∑ i, z i := by
  rw [mem_lattice, ConstructionA.intCast_mem_lattice, Submodule.mem_toAddSubgroup]
  refine and_congr Iff.rfl ⟨fun ⟨k, hk⟩ ↦ ⟨k, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_⟩⟩
  · exact_mod_cast hk
  · exact_mod_cast hk

/-- **The parity form of Construction B.** For a doubly even code, the Construction A vector
`c + 2z`, with `c` the `0`/`1` lift of a codeword, lies in Construction B exactly when `∑ zᵢ` is
even. Together with `ConstructionA.exists_eq_val_add_mul` this describes every Construction B
vector. -/
theorem val_add_two_mul_mem_lattice_iff (hC : BinaryCode.IsDoublyEven C) {c : ι → ZMod 2}
    (hc : c ∈ C) (z : ι → ℤ) :
    (fun i ↦ ((c i).val : ℚ) + 2 * z i) ∈ lattice C ↔ Even (∑ i, z i) := by
  have hcast : (fun i ↦ ((c i).val : ℚ) + 2 * z i) =
      fun i ↦ ((((c i).val : ℤ) + 2 * z i : ℤ) : ℚ) := by
    ext i
    push_cast
    ring
  have hcode : (fun i ↦ ((((c i).val : ℤ) + 2 * z i : ℤ) : ZMod 2)) = c := by
    ext i
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero, ZMod.natCast_zmod_val]
  have hweight : ∑ i, ((c i).val : ℤ) = hammingNorm c := by
    exact_mod_cast sum_val_eq_hammingNorm c
  obtain ⟨a, ha⟩ := BinaryCode.isDoublyEven_iff.mp hC c hc
  rw [hcast, intCast_mem_lattice, hcode, Finset.sum_add_distrib, ← Finset.mul_sum, hweight, ha,
    even_iff_two_dvd]
  push_cast
  simp only [hc, true_and]
  omega

/-- Four times a Construction A vector lies in Construction B. -/
private theorem four_smul_mem_lattice {x : ι → ℚ}
    (hx : x ∈ ConstructionA.lattice 2 C.toAddSubgroup) : (4 : ℤ) • x ∈ lattice C := by
  obtain ⟨z, hz, rfl⟩ := (ConstructionA.mem_lattice 2).mp hx
  refine ⟨Submodule.smul_mem _ _ hx, ∑ i, z i, ?_⟩
  simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring

open scoped Pointwise in
/-- The Construction B carrier is a full lattice: it lies in Construction A and contains four
times every Construction A vector. -/
instance isLattice : (lattice C).IsLattice ℚ := by
  refine Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ
    (M := Units.mk0 (4 : ℚ) (by norm_num) • ConstructionA.lattice 2 C.toAddSubgroup) ?_
    (Submodule.FG.of_le Submodule.IsLattice.fg (lattice_le C))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  simpa only [Units.smul_mk0, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_ofNat] using
    four_smul_mem_lattice C hy

/-! ### Half the coordinate sum -/

/-- **Half the coordinate sum modulo two**, an additive character of the Construction A carrier
of an even binary code. Its kernel is the Construction B carrier, by `ker_sumHalf`. -/
noncomputable def sumHalf (hC : BinaryCode.IsEven C) :
    ConstructionA.lattice 2 C.toAddSubgroup →+ ZMod 2 where
  toFun x := ⌊(∑ i, (x : ι → ℚ) i) / 2⌋
  map_zero' := by simp
  map_add' x y := by
    obtain ⟨k, hk⟩ := ConstructionA.exists_sum_eq_two_mul C hC x.2
    obtain ⟨l, hl⟩ := ConstructionA.exists_sum_eq_two_mul C hC y.2
    simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib, hk, hl]
    rw [show ((2 : ℚ) * k + 2 * l) / 2 = ((k + l : ℤ) : ℚ) by push_cast; ring,
      show (2 : ℚ) * k / 2 = k by ring, show (2 : ℚ) * l / 2 = l by ring]
    rw [Int.floor_intCast, Int.floor_intCast, Int.floor_intCast, Int.cast_add]

/-- `sumHalf` sends a vector of coordinate sum `2k` to `k` modulo two. -/
theorem sumHalf_apply_of_sum_eq (hC : BinaryCode.IsEven C)
    {x : ConstructionA.lattice 2 C.toAddSubgroup} {k : ℤ}
    (hk : ∑ i, (x : ι → ℚ) i = 2 * k) : sumHalf C hC x = k := by
  rw [sumHalf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hk, show (2 : ℚ) * k / 2 = k by ring,
    Int.floor_intCast]

/-- `sumHalf` vanishes exactly on the Construction B carrier. -/
theorem sumHalf_eq_zero_iff (hC : BinaryCode.IsEven C)
    (x : ConstructionA.lattice 2 C.toAddSubgroup) :
    sumHalf C hC x = 0 ↔ (x : ι → ℚ) ∈ lattice C := by
  obtain ⟨k, hk⟩ := ConstructionA.exists_sum_eq_two_mul C hC x.2
  rw [sumHalf_apply_of_sum_eq C hC hk, ZMod.intCast_zmod_eq_zero_iff_dvd, mem_lattice]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨x.2, l, by rw [hk]; push_cast; ring⟩
  · rintro ⟨-, l, hl⟩
    refine ⟨l, ?_⟩
    have : (k : ℚ) = 2 * l := by linarith
    exact_mod_cast this

/-- The kernel of `sumHalf` is the Construction B carrier. -/
theorem ker_sumHalf (hC : BinaryCode.IsEven C) :
    (sumHalf C hC).ker = (lattice C).toAddSubgroup.addSubgroupOf
      (ConstructionA.lattice 2 C.toAddSubgroup).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, sumHalf_eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    Submodule.mem_toAddSubgroup]

/-- `sumHalf` is surjective once there is a coordinate: it sends `2eᵢ` to `1`. -/
theorem sumHalf_surjective [Nonempty ι] (hC : BinaryCode.IsEven C) :
    Function.Surjective (sumHalf C hC) := by
  classical
  intro a
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨a.val • ⟨_, ConstructionA.single_mem_lattice 2 C.toAddSubgroup i⟩, ?_⟩
  rw [map_nsmul, sumHalf_apply_of_sum_eq C hC (k := 1) (by simp), Int.cast_one, nsmul_eq_mul,
    mul_one, ZMod.natCast_zmod_val]

/-- **Construction B has index two in Construction A**, for an even binary code with at least one
coordinate. -/
theorem relIndex_lattice [Nonempty ι] (hC : BinaryCode.IsEven C) :
    (lattice C).toAddSubgroup.relIndex (ConstructionA.lattice 2 C.toAddSubgroup).toAddSubgroup =
      2 := by
  rw [AddSubgroup.relIndex, ← ker_sumHalf C hC, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (sumHalf_surjective C hC), AddSubgroup.card_top,
    Nat.card_zmod]

/-! ### The integral lattice -/

/-- **Construction B** of a self-orthogonal binary linear code, as an integral lattice: the
Construction A vectors whose coordinate sum is divisible by four, with the halved dot product. -/
noncomputable def integralLattice (hC : C.IsSelfOrthogonal) : IntegralLattice (ι → ℚ) :=
  (ConstructionA.integralLattice 2 C.toAddSubgroup
    ((ConstructionA.toZModSubmodule_toAddSubgroup_le_euclideanDual_iff 2 C).mpr hC)).restrictFull
      (lattice C) (by rw [ConstructionA.integralLattice_carrier]; exact lattice_le C)

/-- The carrier of the bundled Construction B lattice. -/
@[simp]
theorem integralLattice_carrier (hC : C.IsSelfOrthogonal) :
    (integralLattice C hC).carrier = lattice C := by
  rw [integralLattice, IntegralLattice.restrictFull_carrier]

/-- The form of the bundled Construction B lattice is the halved dot product of
Construction A. -/
@[simp]
theorem integralLattice_form (hC : C.IsSelfOrthogonal) :
    (integralLattice C hC).form = ConstructionA.form 2 := by
  rw [integralLattice, IntegralLattice.restrictFull_form, ConstructionA.integralLattice_form]

/-- Construction B is nondegenerate, since its form is that of Construction A. -/
instance isNondegenerate_integralLattice (hC : C.IsSelfOrthogonal) :
    (integralLattice C hC).IsNondegenerate :=
  IntegralLattice.instIsNondegenerateRestrictFull _ _ _

/-- Construction B is positive definite. -/
theorem isPosDef_integralLattice (hC : C.IsSelfOrthogonal) :
    (integralLattice C hC).IsPosDef := by
  simpa only [IntegralLattice.IsPosDef, integralLattice_form] using
    ConstructionA.form_posDef 2 (ι := ι)

/-- Construction B has rank equal to the length of the code. -/
@[simp]
theorem finrank_integralLattice (hC : C.IsSelfOrthogonal) :
    Module.finrank ℤ (integralLattice C hC) = Fintype.card ι := by
  rw [IntegralLattice.finrank_carrier, Module.finrank_fintype_fun_eq_card]

/-- **The discriminant of Construction B is four times that of Construction A**, for a
self-orthogonal binary code with at least one coordinate. -/
theorem discriminant_integralLattice [Nonempty ι] (hC : C.IsSelfOrthogonal) :
    (integralLattice C hC).discriminant = 4 * (ConstructionA.integralLattice 2 C.toAddSubgroup
      ((ConstructionA.toZModSubmodule_toAddSubgroup_le_euclideanDual_iff 2 C).mpr
        hC)).discriminant := by
  rw [IntegralLattice.discriminant_eq_mul_relIndex_sq (integralLattice C hC)
    (ConstructionA.integralLattice 2 C.toAddSubgroup
      ((ConstructionA.toZModSubmodule_toAddSubgroup_le_euclideanDual_iff 2 C).mpr hC))
    (by rw [integralLattice_form, ConstructionA.integralLattice_form])
    (by rw [integralLattice_carrier, ConstructionA.integralLattice_carrier]; exact lattice_le C),
    integralLattice_carrier, ConstructionA.integralLattice_carrier,
    relIndex_lattice C (BinaryCode.isEven_of_isSelfOrthogonal hC)]
  ring

/-- **Construction B of a doubly even code is even**, as a sublattice of the even Construction A
lattice. -/
theorem isEven_integralLattice {C : LinearCode (ZMod 2) ι} (hC : BinaryCode.IsDoublyEven C) :
    (integralLattice C hC.isSelfOrthogonal).IsEven :=
  IntegralLattice.isEven_restrictFull (ConstructionA.isEven_integralLattice_two_of_isDoublyEven hC)
    _ _

end TauCeti.ConstructionB
