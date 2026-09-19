/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.PNat.Basic

import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Construction A and its dual lattice

For an additive code `C ≤ (ZMod m)^ι`, `ConstructionA.lattice m C` is the submodule of
`ℚ^ι` consisting of integer vectors whose reductions lie in `C`. The ambient form is
`ConstructionA.form m x y = (∑ i, x i * y i) / m`. This rational model becomes the usual
Construction A lattice after scaling real coordinates by `1 / √m`.

The carrier is a full lattice for every code. Its dual carrier is literally the carrier
constructed from the dual code, so integrality is equivalent to self-orthogonality of the code,
and the resulting integral lattice is unimodular exactly when the code is self-dual.
Additive codes over `ZMod m` are canonically submodules through `AddSubgroup.toZModSubmodule`;
their dual here is the existing `Submodule.euclideanDual`, transported back to an additive
subgroup. The modulus is a positive natural number; no primality hypothesis is needed.
Only nonvanishing of the modulus is used here, as permitted by the AlgebraicCodingTheory
roadmap's standing convention. The type `ℕ+` supplies `NeZero (m : ℕ)` and excludes zero
even in the carrier and form definitions. At `m = 1`, the construction is the integer
coordinate lattice with the ordinary dot product, and the same results apply.

## References

* W. Ebeling, *Lattices and Codes*, §1.3, for binary Construction A.
* A. Munemasa and H. Tamura, *The codes and the lattices of Hadamard matrices*, §4, for the
  integrality criterion over `ZMod m`. The dual-carrier identity is proved directly by testing
  the pairing on the coordinate vectors `m eᵢ` and on integer lifts of codewords.
-/

public section

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ+) {ι : Type*}

/-- The rational carrier of Construction A: the integer vectors reducing to the additive code
`C` modulo `m`. -/
def lattice (m : ℕ+) (C : AddSubgroup (ι → ZMod m)) : Submodule ℤ (ι → ℚ) :=
  (C.toIntSubmodule.comap ((Int.castAddHom (ZMod m)).toIntLinearMap.compLeft ι)).map
    ((Int.castAddHom ℚ).toIntLinearMap.compLeft ι)

/-- Membership in the Construction A carrier is given by an integer lift of a codeword. -/
theorem mem_lattice {C : AddSubgroup (ι → ZMod m)} {x : ι → ℚ} :
    x ∈ lattice m C ↔
      ∃ z : ι → ℤ, (fun i ↦ (z i : ZMod m)) ∈ C ∧ (fun i ↦ (z i : ℚ)) = x :=
  Iff.rfl

/-- An integer vector belongs to Construction A exactly when its reduction is a codeword. -/
@[simp]
theorem intCast_mem_lattice {C : AddSubgroup (ι → ZMod m)} (z : ι → ℤ) :
    (fun i ↦ (z i : ℚ)) ∈ lattice m C ↔ (fun i ↦ (z i : ZMod m)) ∈ C := by
  rw [mem_lattice]
  constructor
  · rintro ⟨w, hw, h⟩
    have : w = z := funext fun i ↦ Int.cast_injective (congrFun h i)
    simpa [this] using hw
  · exact fun h ↦ ⟨z, h, rfl⟩

/-- Inclusion of Construction A carriers is equivalent to inclusion of codes. -/
@[simp]
theorem lattice_le_lattice_iff {C D : AddSubgroup (ι → ZMod m)} :
    lattice m C ≤ lattice m D ↔ C ≤ D := by
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := (Function.Surjective.piMap fun _ ↦ ZMod.intCast_surjective) x
    exact (intCast_mem_lattice m z).mp (h ((intCast_mem_lattice m z).mpr hx))
  · intro h x hx
    obtain ⟨z, hz, rfl⟩ := (mem_lattice m).mp hx
    exact (intCast_mem_lattice m z).mpr (h hz)

/-- The scaled coordinate vectors `m eᵢ` belong to every Construction A carrier. -/
theorem single_mem_lattice [DecidableEq ι] (C : AddSubgroup (ι → ZMod m)) (i : ι) :
    Pi.single i (m : ℚ) ∈ lattice m C := by
  have hcast (R : Type) [Ring R] :
      (fun j ↦ ((Pi.single (M := fun _ : ι ↦ ℤ) i (m : ℤ) j : ℤ) : R)) = Pi.single i (m : R) := by
    simpa using (Pi.single_op (fun _ ↦ Int.cast (R := R))
      (fun _ ↦ Int.cast_zero) i (m : ℤ)).symm
  rw [← hcast ℚ, intCast_mem_lattice, hcast (ZMod m)]
  simp

/-- Every Construction A carrier is a full, finitely generated integer lattice. -/
instance isLattice [Finite ι] (C : AddSubgroup (ι → ZMod m)) : (lattice m C).IsLattice ℚ where
  fg := (IsNoetherian.noetherian _).map _
  span_eq_top := by
    classical
    let := Fintype.ofFinite ι
    apply top_unique
    rw [← (Pi.basisFun ℚ ι).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h := (Submodule.span ℚ (lattice m C : Set (ι → ℚ))).smul_mem
      (m : ℚ)⁻¹ (Submodule.subset_span (single_mem_lattice m C i))
    simpa [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, NeZero.ne (m : ℚ)] using h

variable [Fintype ι]

/-- The rational bilinear form of Construction A, normalized by dividing the dot product by
the modulus. -/
def form (m : ℕ+) : LinearMap.BilinForm ℚ (ι → ℚ) :=
  (m : ℚ)⁻¹ • dotProductBilin ℚ ℚ

/-- The form is the dot product divided by the modulus. -/
@[simp]
theorem form_apply (x y : ι → ℚ) : form m x y = (x ⬝ᵥ y) / m := by
  simp [form, div_eq_mul_inv, mul_comm]

/-- The Construction A form is symmetric. -/
theorem form_isSymm : (form m (ι := ι)).IsSymm := by
  constructor
  intro x y
  simp only [form_apply, dotProduct_comm]

/-- The Construction A form is nondegenerate. -/
theorem form_nondegenerate : (form m (ι := ι)).Nondegenerate := by
  rw [form, TauCeti.BilinForm.nondegenerate_smul_iff
    (IsRegular.of_ne_zero (inv_ne_zero (NeZero.ne (m : ℚ))))]
  exact (dotProductBilin_isPerfPair ℚ ι).nondegenerate

/-- Pairing with `m eᵢ` reads off the `i`th coordinate. -/
@[simp↓]
theorem form_single_right [DecidableEq ι] (x : ι → ℚ) (i : ι) :
    form m x (Pi.single i (m : ℚ)) = x i := by
  simp [form_apply, dotProduct_single, NeZero.ne (m : ℚ)]

/-- Integrality of the Construction A pairing on integer vectors is precisely orthogonality
of their reductions modulo `m`. -/
theorem form_intCast_mem_one_iff (x y : ι → ℤ) :
    form m (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ)) ∈ (1 : Submodule ℤ ℚ) ↔
      (fun i ↦ (x i : ZMod m)) ⬝ᵥ (fun i ↦ (y i : ZMod m)) = 0 := by
  have hcast (R : Type) [CommRing R] :
      (fun i ↦ (x i : R)) ⬝ᵥ (fun i ↦ (y i : R)) = ((x ⬝ᵥ y : ℤ) : R) := by
    exact ((Int.castRingHom R).map_dotProduct x y).symm
  rw [form_apply, hcast ℚ, hcast (ZMod m), ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp h
    refine ⟨z, ?_⟩
    have hz' : (z : ℚ) = (x ⬝ᵥ y : ℤ) / (m : ℚ) := hz
    have := (eq_div_iff (by exact_mod_cast (NeZero.ne (m : ℕ)))).mp hz'
    exact_mod_cast (this.symm.trans (mul_comm _ _))
  · rintro ⟨z, hz⟩
    apply Submodule.mem_one.mpr
    refine ⟨z, ?_⟩
    simp [hz, NeZero.ne (m : ℚ)]

/-- The dual of a Construction A carrier is the Construction A carrier of the Euclidean dual
code, as an equality of submodules of the same rational coordinate space. -/
theorem dualSubmodule_lattice (C : AddSubgroup (ι → ZMod m)) :
    (form m).dualSubmodule (lattice m C) =
      lattice m (AddSubgroup.toZModSubmodule m C).euclideanDual.toAddSubgroup := by
  classical
  ext x
  rw [LinearMap.BilinForm.mem_dualSubmodule, mem_lattice]
  constructor
  · intro hx
    have hint (i : ι) : ∃ z : ℤ, (z : ℚ) = x i := by
      have h := hx (Pi.single i (m : ℚ)) (single_mem_lattice m C i)
      rw [form_single_right] at h
      exact Submodule.mem_one.mp h
    choose z hz using hint
    refine ⟨z, ?_, funext hz⟩
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_euclideanDual']
    intro y hy
    obtain ⟨w, rfl⟩ := (Function.Surjective.piMap fun _ ↦ ZMod.intCast_surjective) y
    apply (form_intCast_mem_one_iff m z w).mp
    rw [funext hz]
    exact hx _ ((intCast_mem_lattice m w).mpr hy)
  · rintro ⟨z, hz, rfl⟩ y hy
    obtain ⟨w, hw, rfl⟩ := (mem_lattice m).mp hy
    apply (form_intCast_mem_one_iff m z w).mpr
    exact Submodule.mem_euclideanDual'.mp hz _ hw

/-- The Construction A form is integral on its carrier exactly when the additive code is
self-orthogonal for the dot product modulo `m`. -/
theorem lattice_le_dualSubmodule_iff (C : AddSubgroup (ι → ZMod m)) :
    lattice m C ≤ (form m).dualSubmodule (lattice m C) ↔
      AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [dualSubmodule_lattice, lattice_le_lattice_iff]
  rfl

/-- Construction A as an integral lattice, under the exact self-orthogonality hypothesis. -/
def integralLattice (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    IntegralLattice (ι → ℚ) :=
  IntegralLattice.ofSubmodule (lattice m C) (form m) (form_isSymm m)
    ((lattice_le_dualSubmodule_iff m C).mpr hC)

/-- The underlying carrier of the bundled Construction A lattice. -/
@[simp]
theorem integralLattice_carrier (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).carrier = lattice m C := by
  simp [integralLattice]

/-- The ambient form of the bundled Construction A lattice. -/
@[simp]
theorem integralLattice_form (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).form = form m := by
  simp [integralLattice]

/-- A self-orthogonal code gives a nondegenerate integral lattice. -/
instance integralLattice_isNondegenerate (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).IsNondegenerate where
  nondegenerate := by rw [integralLattice_form]; exact form_nondegenerate m

/-- An integral Construction A lattice is unimodular exactly when its code is self-dual. -/
theorem integralLattice_isUnimodular_iff (C : AddSubgroup (ι → ZMod m))
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual) :
    (integralLattice m C hC).IsUnimodular ↔
      AddSubgroup.toZModSubmodule m C = (AddSubgroup.toZModSubmodule m C).euclideanDual := by
  rw [IntegralLattice.isUnimodular_iff_dualCarrier_le, IntegralLattice.dualCarrier,
    integralLattice_form, integralLattice_carrier, dualSubmodule_lattice, lattice_le_lattice_iff]
  exact ⟨fun h ↦ le_antisymm hC h, fun h ↦ h.ge⟩

end TauCeti.ConstructionA
