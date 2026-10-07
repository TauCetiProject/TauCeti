/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Field

/-!
# The real normalization of Construction A

The rational Construction A form divides the dot product by the positive modulus `m`.
Multiplying real coordinates by `1 / √m` instead gives the ordinary dot product.
This file identifies the scalar extension `ℝ ⊗[ℚ] (ι → ℚ)` with `ι → ℝ` by a bilinear
isometry and identifies the image of the rational lattice with the usual real Construction A
carrier: the vectors `z / √m` whose integer coordinates reduce to a codeword.

The comparison applies to every additive code, without self-orthogonality. When the code is
self-orthogonal it also identifies the carrier and form of the bundled integral lattice.
The modulus is positive throughout, and the coordinate type is arbitrary and finite for
the full-lattice instance, scalar extension, and bilinear forms.

The normalization follows Harada–Munemasa–Venkov, *Classification of ternary extremal
self-dual codes of length 28*, §2, and Munemasa–Tamura, *The codes and the lattices of
Hadamard matrices*, §4. The scalar-extension equivalence uses Mathlib's
`TensorProduct.piScalarRight`.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ+) {ι : Type*}

/-- The rational-linear embedding into real coordinates scaled by `1 / √m`. -/
def realEmbedding : (ι → ℚ) →ₗ[ℚ] (ι → ℝ) :=
  (Real.sqrt (m : ℝ))⁻¹ • (Algebra.linearMap ℚ ℝ).compLeft ι

/-- The normalized real embedding divides every coordinate by `√m`. -/
@[simp]
theorem realEmbedding_apply (x : ι → ℚ) (i : ι) :
    realEmbedding m x i = (x i : ℝ) / Real.sqrt (m : ℝ) := by
  simp [realEmbedding, div_eq_mul_inv, mul_comm]

/-- The real normalization is injective. -/
theorem realEmbedding_injective : Function.Injective (realEmbedding m (ι := ι)) := by
  intro x y h
  funext i
  have hcoord := congrFun h i
  simp only [realEmbedding_apply] at hcoord
  exact Rat.cast_injective ((div_left_inj' (Real.sqrt_ne_zero'.mpr
    (by exact_mod_cast m.pos))).mp hcoord)

/-- The real Construction A carrier is the normalized image of its rational carrier. -/
def realLattice (C : AddSubgroup (ι → ZMod m)) : Submodule ℤ (ι → ℝ) :=
  (lattice m C).map ((realEmbedding m).restrictScalars ℤ)

/-- A real vector belongs to Construction A exactly when it is an integer lift of a codeword,
divided coordinatewise by `√m`. -/
theorem mem_realLattice {C : AddSubgroup (ι → ZMod m)} {x : ι → ℝ} :
    x ∈ realLattice m C ↔
      ∃ z : ι → ℤ, (fun i ↦ (z i : ZMod m)) ∈ C ∧
        (fun i ↦ (z i : ℝ) / Real.sqrt (m : ℝ)) = x := by
  simp only [realLattice, Submodule.mem_map, mem_lattice]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by ext i; simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun i ↦ (z i : ℚ), ⟨z, hz, rfl⟩, by ext i; simp⟩

/-- Normalizing an integer vector gives a real lattice vector exactly when its reduction
belongs to the code. -/
@[simp]
theorem intCast_div_sqrt_mem_realLattice {C : AddSubgroup (ι → ZMod m)} (z : ι → ℤ) :
    (fun i ↦ (z i : ℝ) / Real.sqrt (m : ℝ)) ∈ realLattice m C ↔
      (fun i ↦ (z i : ZMod m)) ∈ C := by
  rw [mem_realLattice]
  constructor
  · rintro ⟨w, hw, h⟩
    have hwz : w = z := by
      funext i
      exact Int.cast_injective ((div_left_inj' (Real.sqrt_ne_zero'.mpr
        (by exact_mod_cast m.pos))).mp (congrFun h i))
    simpa [hwz] using hw
  · exact fun hz ↦ ⟨z, hz, rfl⟩

/-- For finite coordinates, the real Construction A carrier is a full, finitely generated
lattice in `ι → ℝ`. -/
instance isLattice_realLattice [Finite ι] (C : AddSubgroup (ι → ZMod m)) :
    (realLattice m C).IsLattice ℝ where
  fg := (Submodule.IsLattice.fg (A := ℚ) (M := lattice m C)).map _
  span_eq_top := by
    classical
    let := Fintype.ofFinite ι
    apply top_unique
    rw [← (Pi.basisFun ℝ ι).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast m.pos)
    have h := (Submodule.span ℝ (realLattice m C : Set (ι → ℝ))).smul_mem
      (Real.sqrt (m : ℝ) / m) (Submodule.subset_span (Submodule.mem_map_of_mem
        (f := (realEmbedding m).restrictScalars ℤ) (single_mem_lattice m C i)))
    convert h using 1
    congr! 1
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [field]
    · simp [hj]

variable [Fintype ι]

/-- The real embedding carries the rational normalized form to the ordinary real dot product. -/
theorem dotProduct_realEmbedding (x y : ι → ℚ) :
    realEmbedding m x ⬝ᵥ realEmbedding m y = (form m x y : ℝ) := by
  simp only [dotProduct, realEmbedding_apply, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity), ← Finset.sum_div,
    form_apply, dotProduct, Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]

/-- Real scalar extension followed by the normalization `1 / √m`. -/
private def realScalarExtensionEquiv : ℝ ⊗[ℚ] (ι → ℚ) ≃ₗ[ℝ] (ι → ℝ) := by
  classical
  exact (TensorProduct.piScalarRight ℚ ℝ ℝ ι).trans
    (LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (Real.sqrt (m : ℝ))⁻¹
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast m.pos))))

/-- The scalar-extension equivalence sends a pure tensor to its scaled coordinate vector. -/
private theorem realScalarExtensionEquiv_tmul (r : ℝ) (x : ι → ℚ) (i : ι) :
    realScalarExtensionEquiv m (r ⊗ₜ[ℚ] x) i = r * realEmbedding m x i := by
  classical
  simp [realScalarExtensionEquiv, realEmbedding_apply, div_eq_mul_inv,
    Algebra.smul_def, mul_comm, mul_assoc]

omit [Fintype ι] in
/-- The normalized real embedding realizes extension of scalars from `ℚ` to `ℝ`. -/
theorem isBaseChange_realEmbedding [Finite ι] : IsBaseChange ℝ (realEmbedding m (ι := ι)) := by
  classical
  let _ : Fintype ι := .ofFinite ι
  refine IsBaseChange.of_equiv (realScalarExtensionEquiv m) fun x ↦ ?_
  ext i
  simp [realScalarExtensionEquiv_tmul]

/-- The scalar extension of the rational Construction A space is bilinearly isometric to the
ordinary real coordinate space. -/
def realNormalizationIsometry :
    ((form m (ι := ι)).baseChange ℝ).IsometryEquiv (dotProductBilin (m := ι) ℝ ℝ) where
  toLinearEquiv := (isBaseChange_realEmbedding m).equiv
  map_app' := (isBaseChange_realEmbedding m).bilinForm_baseChange (form m)
    (dotProductBilin ℝ ℝ) (fun x y ↦ by simpa using dotProduct_realEmbedding m x y)

/-- The normalization isometry acts by the scalar-extension equivalence of the real embedding. -/
@[simp]
theorem realNormalizationIsometry_apply (x : ℝ ⊗[ℚ] (ι → ℚ)) :
    realNormalizationIsometry m x = (isBaseChange_realEmbedding m).equiv x := (rfl)

/-- The isometry sends the embedded rational lattice onto the usual real Construction A
carrier, with precisely the integer lifts of codewords as its vectors. -/
theorem image_realNormalizationIsometry_lattice (C : AddSubgroup (ι → ZMod m)) :
    (fun x ↦ realNormalizationIsometry m (1 ⊗ₜ[ℚ] x)) '' (lattice m C : Set (ι → ℚ)) =
      (realLattice m C : Set (ι → ℝ)) := by
  have h (x : ι → ℚ) : realNormalizationIsometry m (1 ⊗ₜ[ℚ] x) = realEmbedding m x := by
    ext i
    simp
  simp only [h, realLattice, Submodule.map_coe, LinearMap.coe_restrictScalars]

end TauCeti.ConstructionA
